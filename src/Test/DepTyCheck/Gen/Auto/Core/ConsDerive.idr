||| Several tactics for derivation of particular generators for a constructor regarding to how they use externals
module Test.DepTyCheck.Gen.Auto.Core.ConsDerive

import public Control.Monad.State

import public Data.Either

import public Debug.Reflection

import public Decidable.Equality

import public Test.DepTyCheck.Gen.Auto.Derive

%default total

-------------------------------------------------
--- Derivation of a generator for constructor ---
-------------------------------------------------

--- Interface ---

public export
interface ConstructorDerivator where
  consGenExpr : CanonicGen m => GenSignature -> (con : Con) -> (given : SortedSet $ Fin con.args.length) -> (fuel : TTImp) -> m TTImp

--- Particular tactics ---

||| "Non-obligatory" means that some present external generator of some type
||| may be ignored even if its type is really used in a generated data constructor.
namespace NonObligatoryExts

  ||| Least-effort non-obligatory tactic is one which *does not use externals* during taking a decision on the order.
  ||| It uses externals if decided order happens to be given by an external generator, but is not obliged to use any.
  ||| It is seemingly most simple to implement, maybe the fastest and
  ||| fits well when external generators are provided for non-dependent types.
  export
  [LeastEffort] ConstructorDerivator where
    consGenExpr sig con givs fuel = do

      -------------------------------------------------------------
      -- Prepare intermediate data and functions using this data --
      -------------------------------------------------------------

      -- Get file position of the constructor definition (for better error reporting)
      let conFC = getFC con.type

      -- Build a map from constructor's argument name to its index
      let conArgIdxs = SortedMap.fromList $ mapI' con.args $ \idx, arg => (argName arg, idx)

      -- Analyse that we can do subgeneration for each constructor argument
      -- Fails using `Elaboration` if the given expression is not an application to a type constructor
      let analyseTypeApp : TTImp -> m TypeApp
          analyseTypeApp expr = do
            let (lhs, args) = unAppAny expr
            let IVar _ lhsName = lhs
              | _ => failAt (getFC lhs) "Only applications to a name is supported, given \{show lhs}"
            ty <- try .| getInfo' lhsName
                      .| failAt (getFC lhs) "Only applications to type constructors are supported at the moment"
            pure $ MkTypeApp ty $ Vect.fromList ty.args <&> \arg => case arg.type of
              expr@(IVar _ n) => mirror . maybeToEither expr $ lookup n conArgIdxs
              expr            => Right expr

      -- Compute left-to-right need of generation when there are non-trivial types at the left
      argsTypeApps <- for .| Vect.fromList con.args .| analyseTypeApp . type

      -- Derive constructor calling expression for given order of generation
      let genForOrder : List (Fin con.args.length) -> m TTImp
          genForOrder = map (`apply` callCons) . evalStateT givs . foldlM genForOneArg id where

            bindName : forall m. Elaboration m => Name -> m TTImp
            bindName $ UN $ Basic n = pure $ bindVar n
            bindName n = failAt conFC "Unsupported name \{show n} for the basement of a bind name"

            -- ... state is the set of arguments that are already present (given or generated)
            genForOneArg : (TTImp -> TTImp) -> (gened : Fin con.args.length) -> StateT (SortedSet $ Fin con.args.length) m $ TTImp -> TTImp
            genForOneArg leftExprF genedArg = do

              -- Get info for the `genedArg`
              let MkTypeApp typeOfGened argsOfTypeOfGened = index genedArg $ the (Vect _ TypeApp) argsTypeApps

              -- Acquire the set of arguments that are already present
              presentArguments <- get

              -- TODO to put the following check as up as possible as soon as it typecheks O_O
              -- Check that those argument that we need to generate is not already present
              let False = contains genedArg presentArguments
                | True => pure leftExprF

              -- Filter arguments classification according to the set of arguments that are left to be generated;
              -- Those which are `Right` are given, those which are `Left` are needs to be generated.
              let depArgs : Vect typeOfGened.args.length (Either (Fin con.args.length) TTImp) := argsOfTypeOfGened <&> \case
                Right expr => Right expr
                Left i     => if contains i presentArguments then Right $ var $ argName $ index' con.args i else Left i

              -- Determine which arguments will be on the left of dpair in subgen call, in correct order
              let subgeneratedArgs = mapMaybe getLeft $ toList depArgs

              -- Make sure generated arguments will not be generated again
              modify $ union $ fromList subgeneratedArgs

              -- Form a task for subgen
              let (subgivensLength ** subgivens) = mapMaybe (\(ie, idx) => (idx,) <$> getRight ie) $ depArgs `zip` allFins'
              let subsig : GenSignature := MkGenSignature typeOfGened $ fromList $ fst <$> toList subgivens
              let Yes subsigGivensLength = decEq subsig.givenParams.asList.length subgivensLength
                | No _ => fail "INTERNAL ERROR: error in given params set length computation"

              -- Form an expression to call the subgen
              subgenCall <- lift $ callGen subsig fuel $ rewrite subsigGivensLength in snd <$> subgivens

              -- Form an expression of binding the result of subgen
              bindArgs <- subgeneratedArgs ++ [genedArg] `for` bindName . argName . index' con.args
              let bindSubgenResult = appAll `{Builtin.DPair.MkDPair} bindArgs

              -- Chain the subgen call with a given continuation
              pure $ \cont => `(~(subgenCall) >>= \ ~(bindSubgenResult) => ~(leftExprF cont))

            callCons : TTImp
            callCons = `(Prelude.pure ~(callCon con $ fromList con.args <&> var . name))

      -------------------------------------------------
      -- Left-to-right generation phase (2nd phase) ---
      -------------------------------------------------

      --------------------------------------------------------------------------------
      -- Preparation of input for the left-to-right phase (1st right-to-left phase) --
      --------------------------------------------------------------------------------

      ---------------------------------------------------------------------------------
      -- Main right-to-left generation phase (3rd phase aka 2nd right-to-left phase) --
      ---------------------------------------------------------------------------------

      -- Get dependencies of constructor's arguments
      deps <- downmap ((`difference` givs) . mapIn weakenToSuper) <$> argDeps con.args

      -- Arguments that no other argument depends on
      let rightmostArgs = fromFoldable {f=Vect _} allFins' `difference` (givs `union` concat deps)

      ---------------------------------------------------------------
      -- Manage different possible variants of generation ordering --
      ---------------------------------------------------------------

      -- Acquire order(s) in what we will generate arguments
      -- TODO to permute independent groups of arguments independently
      let allOrders = allPermutations rightmostArgs

      map callOneOf $ traverse genForOrder $ forget allOrders

      where

        -- TODO make this to be a `record` as soon as #2177 is fixed
        data TypeApp : Type where
          MkTypeApp :
            (type : TypeInfo) ->
            (argTypes : Vect type.args.length .| Either (Fin con.args.length) TTImp) ->
            TypeApp

  ||| Best effort non-obligatory tactic tries to use as much external generators as possible
  ||| but discards some there is a conflict between them.
  ||| All possible non-conflicting layouts may be produced in the generated values list.
  |||
  ||| E.g. when we have external generators ``(a : _) -> (b : T ** C a b)`` and ``(b : T ** D b)`` and
  ||| a constructor of form ``C a b -> D b -> ...``, we can use values from both pairs
  ||| ``(a : _) -> (b : T ** C a b)`` with ``(b : T) -> D b`` and
  ||| ``(a : _) -> (b : T) -> C a b`` with ``(b : T ** D b)``,
  ||| i.e. to use both of external generators to form the generated values list
  ||| but not obligatorily all the external generators at the same time.
  export
  [BestEffort] ConstructorDerivator where
    consGenExpr sig con givs fuel = do
      ?cons_body_besteff_nonoblig_rhs

||| "Obligatory" means that is some external generator is present and a constructor has
||| an argument of a type which is generated by this external generator, it must be used
||| in the constuctor's generator.
|||
||| Dependent types are important here, i.e. generator ``(a : _) -> (b ** C a b)``
||| is considered to be a generator for the type ``C``.
||| The problem with obligatory generators is that some external generators may be incompatible.
|||
|||   E.g. once we have ``(a : _) -> (b ** C a b)`` and ``(a ** b ** C a b)`` at the same time,
|||   once ``C`` is used in the same constructor, we cannot guarantee that we will use both external generators.
|||
|||   The same problem is present once we have external generators for ``(a : _) -> (b : T ** C a b)`` and ``(b : T ** D b)`` at the same time,
|||   and both ``C`` and ``D`` are used in the same constructor with the same parameter of type ``T``,
|||   i.e. when constructor have something like ``C a b -> D b -> ...``.
|||
|||   Notice, that this problem does not arise in constructors of type ``C a b1 -> D b2 -> ...``
|||
||| In this case, we cannot decide in general which value of type ``T`` to be used for generation is we have to use both generators.
||| We can either fail to generate a value for such constructor (``FailFast`` tactic),
||| or alternatively we can try to match all the generated values of type ``T`` from both generators
||| using ``DecEq`` and leave only intersection (``DecEqConflicts`` tactic).
namespace ObligatoryExts

  export
  [FailFast] ConstructorDerivator where
    consGenExpr sig con givs fuel = do
      ?cons_body_obl_ff_rhs

  export
  [DecEqConflicts] ConstructorDerivator where
    consGenExpr sig con givs fuel = do
      ?cons_body_obl_deceq_rhs
