||| Several tactics for derivation of particular generators for a constructor regarding to how they use externals
module Test.DepTyCheck.Gen.Auto.Core.Cons

import public Data.List.Equalities
import public Data.Vect.Extra

import public Debug.Reflection

import public Decidable.Equality

import public Test.DepTyCheck.Gen.Auto.Derive

import public Test.DepTyCheck.Gen.Auto.Util.Collections

%default total

-----------------------------------------
--- Utility functions and definitions ---
-----------------------------------------

--- Expressions generation utils ---

defArgNames : {sig : GenSignature} -> Vect sig.givenParams.asList.length String
defArgNames = sig.givenParams.asVect <&> show . name . index' sig.targetType.args

export %inline
canonicDefaultLHS : GenSignature -> Name -> (fuel : String) -> TTImp
canonicDefaultLHS sig n fuel = callCanonic sig n .| bindVar fuel .| bindVar <$> defArgNames

export %inline
canonicDefaultRHS : GenSignature -> Name -> (fuel : TTImp) -> TTImp
canonicDefaultRHS sig n fuel = callCanonic sig n fuel .| varStr <$> defArgNames

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
-- TODO to use set for the free names at input
-- TODO to think of using again `Fin n -> String` instead of `Vect n String` because of ease of splitting
export
analyseDeepConsApp : Elaboration m =>
                     (freeNames : List Name) ->
                     (analysedExpr : TTImp) ->
                     m $ Maybe (appliedFreeNames : List Name ** (bindExpr : Vect appliedFreeNames.length TTImp) -> {-bind expression-} TTImp)
analyseDeepConsApp freeNames e = try (Just <$> isD e) (pure Nothing) where

  isD : TTImp -> Elab (appliedFreeNames : List Name ** Vect appliedFreeNames.length TTImp -> TTImp)
  isD e = do

    -- Treat given expression as a function application to some name
    let (IVar _ lhsName, args) = unAppAny e
      | _ => fail "Not an application for some variable"

    -- Check if this is a free name
    let False = lhsName `elem` freeNames
      | True => if null args
                  then pure (singleton lhsName ** index FZ)
                  else fail "Applying free name to some arguments"

    -- Check that this is an application to a constructor's name
    _ <- getCon lhsName -- or fail if `lhsName` is not a constructor

    -- Analyze deeply all the arguments
    deepArgs <- for args $ \anyApp => map (anyApp,) $ isD $ assert_smaller e $ getExpr anyApp

    -- Collect all the applied names and form proper application expression with binding variables
    pure $ foldl mergeApp ([] ** const $ var lhsName) deepArgs

    where
      mergeApp : (namesL : List Name ** Vect namesL.length a -> TTImp) ->
                 (AnyApp, (namesR : List Name ** Vect namesR.length a -> TTImp)) ->
                 (names : List Name ** Vect names.length a -> TTImp)
      mergeApp (namesL ** bindL) (anyApp, (namesR ** bindR)) = MkDPair (namesL ++ namesR) $ \bindNames => do
        let bindNames : Vect (namesL.length + namesR.length) a := rewrite sym $ lengthDistributesOverAppend namesL namesR in bindNames
        let (bindNamesL, bindNamesR) = splitAt namesL.length bindNames
        let (lhs, rhs) = (bindL bindNamesL, bindR bindNamesR)
        reAppAny1 lhs $ const rhs `mapExpr` anyApp

--- Interface ---

public export
interface ConstructorDerivator where
  -- TODO to add appropriate post-index-analysis parameters
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
  let conArgNames = (.name) <$> con.args

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
    let bindVarNames = flip mapWithPos (Vect.fromList appliedArgs) $ \pos, name => "\{show name}_arg_\{show idx}_pos_\{show pos}"
    pure $ the (TTImp, (appArgs : List Name ** Vect appArgs.length String)) $
      (bindExprF $ bindVar <$> bindVarNames, (appliedArgs ** bindVarNames))

  -- Acquire LHS bind expressions for the given parameters
  let givenBindExprs = fst <$> deepConsApps

  -- Determine renaming map and pairs of names which should be `decEq`'ed

  ?fop_check_con_args

  -- TODO to build a map from a name to `Fin con.args.length`

  -- TODO to form a list of given constructor arguments to `consGenExpr` call

  let fuelArg = "fuel_cons_arg"
  pure [ canonicDefaultLHS sig name fuelArg .= !(consGenExpr sig con ?con_givens $ varStr fuelArg) ]

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
