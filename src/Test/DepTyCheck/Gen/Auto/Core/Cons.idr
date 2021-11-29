||| Several tactics for derivation of particular generators for a constructor regarding to how they use externals
module Test.DepTyCheck.Gen.Auto.Core.Cons

import public Control.Monad.State.Tuple

import public Data.Fin.Extra
import public Data.List.Equalities
import public Data.Vect.Extra

import public Debug.Reflection

import public Decidable.Equality

import public Test.DepTyCheck.Gen.Auto.Derive

import public Test.DepTyCheck.Gen.Auto.Util.Collections

%default total

-------------------------------------------------
--- Derivation of a generator for constructor ---
-------------------------------------------------

--- Utilities ---

||| Analyses whether the given expression can be an expression of free variables applies (maybe deeply) to a number of data constructors.
|||
||| Returns which of given free names are actually used in the given expression, in order of appearance in the expression.
||| Notice that applied free names may repeat as soon as one name is used several times in the given expression.
|||
||| Also, a function returning a bind expression (an expression replacing all free names with bind names (`IBindVar`))
||| is also returned.
||| This function requires bind variable names as input.
||| It returns correct bind expression only when all given bind names are different.
export
analyseDeepConsApp : Elaboration m =>
                     (freeNames : SortedSet Name) ->
                     (analysedExpr : TTImp) ->
                     m $ Maybe (appliedFreeNames : List Name ** (bindExpr : Fin appliedFreeNames.length -> TTImp) -> {-bind expression-} TTImp)
analyseDeepConsApp freeNames e = try (Just <$> isD e) (pure Nothing) where

  isD : TTImp -> Elab (appliedFreeNames : List Name ** (Fin appliedFreeNames.length -> TTImp) -> TTImp)
  isD e = do

    -- Treat given expression as a function application to some name
    let (IVar _ lhsName, args) = unAppAny e
      | _ => fail "Not an application for some variable"

    -- Check if this is a free name
    let False = contains lhsName freeNames
      | True => if null args
                  then pure (singleton lhsName ** \f => f FZ)
                  else fail "Applying free name to some arguments"

    -- Check that this is an application to a constructor's name
    _ <- getCon lhsName -- or fail if `lhsName` is not a constructor

    -- Analyze deeply all the arguments
    deepArgs <- for args $ \anyApp => map (anyApp,) $ isD $ assert_smaller e $ getExpr anyApp

    -- Collect all the applied names and form proper application expression with binding variables
    pure $ foldl mergeApp ([] ** const $ var lhsName) deepArgs

    where
      mergeApp : (namesL : List Name ** (Fin namesL.length -> a) -> TTImp) ->
                 (AnyApp, (namesR : List Name ** (Fin namesR.length -> a) -> TTImp)) ->
                 (names : List Name ** (Fin names.length -> a) -> TTImp)
      mergeApp (namesL ** bindL) (anyApp, (namesR ** bindR)) = MkDPair (namesL ++ namesR) $ \bindNames => do
        let bindNames : Fin (namesL.length + namesR.length) -> a := rewrite sym $ lengthDistributesOverAppend namesL namesR in bindNames
        let lhs = bindL $ bindNames . indexSum . Left
        let rhs = bindR $ bindNames . indexSum . Right
        reAppAny1 lhs $ const rhs `mapExpr` anyApp

--- Interface ---

public export
interface ConstructorDerivator where
  consGenExpr : CanonicGen m => GenSignature -> (con : Con) -> (given : SortedSet $ Fin con.args.length) -> (fuel : TTImp) -> m TTImp

--- Entry function ---

export
canonicConsBody : ConstructorDerivator => CanonicGen m => GenSignature -> Name -> Con -> m $ List Clause
canonicConsBody sig name con = do

  -- Acquire constructor's return type arguments
  let conRetTypeArgs = snd $ unAppAny con.type
  conRetTypeArgs <- for conRetTypeArgs $ \case -- resembles similar management from `Entry` module; they must be consistent
    PosApp e     => pure e
    NamedApp _ _ => fail "Named implicit applications are not supported yet as in `\{show con.name}`"
    AutoApp _    => fail "Auto-implicit applications are not supported yet as in `\{show con.name}`"
    WithApp _    => fail "Unexpected `with` application in the constructor's `\{show con.name}` return type"

  -- Match lengths of `conRetTypeArgs` and `sig.targetType.args`
  let Yes conRetTypeArgsLengthCorrect = conRetTypeArgs.length `decEq` sig.targetType.args.length
    | No _ => fail "INTERNAL ERROR: length of the return type of constructor `\{show con.name}` does not equal to the type's arguments count"

  let conRetTypeArg : Fin sig.targetType.args.length -> TTImp
      conRetTypeArg idx = index' conRetTypeArgs $ rewrite conRetTypeArgsLengthCorrect in idx

  -- Determine names of the arguments of the constructor (as a function)
  let conArgNames = fromList $ (.name) <$> con.args

  -- For given arguments, determine whether they are
  --   - just a free name
  --   - repeated name of another given parameter (need of `decEq`)
  --   - (maybe, deeply) constructor call (need to match)
  --   - function call on a free param (need to use "inverted function" filtering trick)
  --   - something else (cannot manage yet)
  deepConsApps <- for (Vect.fromList sig.givenParams.asList) $ \idx => do
    let argExpr = conRetTypeArg idx
    Just (appliedArgs ** bindExprF) <- analyseDeepConsApp conArgNames argExpr
      | Nothing => fail "Argument #\{show idx} of constructor \{show con.name} is not supported yet (argument expression: \{show argExpr})"
                   -- TODO to do `failAt` with nice position
    pure $ the (appArgs : List Name ** (Fin appArgs.length -> TTImp) -> TTImp) $
      (appliedArgs ** bindExprF)

  -- Acquire LHS bind expressions for the given parameters
  -- Determine pairs of names which should be `decEq`'ed
  let getAndInc : forall m. MonadState Nat m => m Nat
      getAndInc = get <* modify S
  ((givenConArgs, decEqedNames, _), bindExprs) <-
    runStateT (empty, empty, 0) {stateType=(SortedSet String, SortedSet (String, String), Nat)} {m} $
      for deepConsApps $ \(appliedNames ** bindExprF) => do
        renamedAppliedNames <- for (Vect.fromList appliedNames) $ \case
          UN (Basic name) => if contains name !get
            then do
              let substName = "to_be_deceqed__" ++ name ++ show !getAndInc
              modify $ insert (name, substName)
              pure substName
            else modify (insert name) $> name
          badName => fail "Unsupported name `\{show badName}` of a parameter used in the constructor `\{show con.name}`"
        pure $ bindExprF $ bindVar . flip index renamedAppliedNames

  -- Build a map from constructor's argument name to its index
  let conArgIdxs = SortedMap.fromList $ mapI' con.args $ \idx, arg => (argName arg, idx)

  -- Determine indices of constructor's arguments that are given
  givenConArgs <- for givenConArgs.asList $ \givenArgNameStr => do
    let Just idx = lookup (UN $ Basic givenArgNameStr) conArgIdxs
      | Nothing => fail "INTERNAL ERROR: calculated given `\{givenArgNameStr}` is not found in an arguments list of the constructor `\{show con.name}`"
    pure idx

  -- Equalise index values which must be propositionally equal to some parameters
  let enrich1WithDecEq : (String, String) -> TTImp -> TTImp
      enrich1WithDecEq (l, r) subexpr = `(
          case Decidable.Equality.decEq ~(varStr l) ~(varStr r) of
            Prelude.No  _            => Prelude.empty
            Prelude.Yes Builtin.Refl => ~(subexpr)
        )
      deceqise : TTImp -> TTImp
      deceqise = foldr (\ss, f => enrich1WithDecEq ss . f) id decEqedNames

  -- Form the declaration cases of a function generating values of particular constructor
  let fuelArg = "fuel_cons_arg"
  pure $
    -- Happy case, given arguments conform out constructor's GADT indices
    [ callCanonic sig name (bindVar fuelArg) bindExprs .= deceqise !(consGenExpr sig con .| fromList givenConArgs .| varStr fuelArg) ]
    ++ if all isSimpleBindVar bindExprs then [] {- do not produce dead code if the happy case handles everything already -} else
      -- The rest case, if given arguments do not conform to the current constructor then return empty generator
      [ callCanonic sig name implicitTrue (replicate _ implicitTrue) .= `(empty) ]

--- Particular tactics ---

||| "Non-obligatory" means that some present external generator of some type
||| may be ignored even if its type is really used in a generated data constructor.
namespace NonObligatoryExts

  ||| Leat effort non-obligatory tactic is one which *does not use externals* during taking a decision on the order.
  ||| It uses externals if decided order happens to be given by an external generator, but is not obliged to use any.
  ||| It is seemingly most simple to implement, maybe the fastest and
  ||| fits well when external generators are provided for non-dependent types.
  export
  [LeastEffort] ConstructorDerivator where
    consGenExpr sig con givs fuel = do

      -- Get dependencies of constructor's arguments
      deps <- argDeps con.args
      let weakenedDeps : Vect _ $ SortedSet $ Fin _ := flip downmapI deps $ \_ => mapIn weakenToSuper

      -- Arguments that no other argument depends on
      let kingArgs = fromFoldable (allFins' _) `difference` concat weakenedDeps

      -- Acquire order(s) in what we will generate arguments
      -- TODO to permute independent groups of arguments independently
      let allKingsOrders = allPermutations kingArgs

      let genForKingsOrder : List (Fin con.args.length) -> m TTImp
          genForKingsOrder kings = ?genForKingsOrder_rhs

      map callOneOf $ traverse genForKingsOrder $ forget allKingsOrders

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
