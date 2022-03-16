||| Derivation of the outer layer of a constructor-generating function, performing GADT indices check of given arguments.
module Test.DepTyCheck.Gen.Auto.Core.ConsEntry

import public Control.Monad.State.Tuple

import public Debug.Reflection

import public Decidable.Equality

import public Test.DepTyCheck.Gen.Auto.Core.ConsDerive
import public Test.DepTyCheck.Gen.Auto.Core.Util

%default total

-------------------------------------------------
--- Derivation of a generator for constructor ---
-------------------------------------------------

--- Entry function ---

export
canonicConsBody : ConstructorDerivator => CanonicGen m => GenSignature -> Name -> Con -> m $ List Clause
canonicConsBody sig name con = do

  -- Get file position of the constructor definition (for better error reporting)
  let conFC = getFC con.type

  -- Acquire constructor's return type arguments
  let conRetTypeArgs = snd $ unAppAny con.type
  conRetTypeArgs <- for conRetTypeArgs $ \case -- resembles similar management from `Entry` module; they must be consistent
    PosApp e     => pure e
    NamedApp _ _ => failAt conFC "Named implicit applications are not supported yet"
    AutoApp _    => failAt conFC "Auto-implicit applications are not supported yet"
    WithApp _    => failAt conFC "Unexpected `with` application in the constructor's return type"

  -- Match lengths of `conRetTypeArgs` and `sig.targetType.args`
  let Yes conRetTypeArgsLengthCorrect = conRetTypeArgs.length `decEq` sig.targetType.args.length
    | No _ => failAt conFC "INTERNAL ERROR: length of the return type does not equal to the type's arguments count"

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
      | Nothing => failAt conFC "Argument #\{show idx} is not supported yet (argument expression: \{show argExpr})"
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
              -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
              let substName = "to_be_deceqed^^" ++ name ++ show !getAndInc
              modify $ insert (name, substName)
              pure substName
            else modify (insert name) $> name
          badName => failAt conFC "Unsupported name `\{show badName}` of a parameter used in the constructor"
        pure $ bindExprF $ bindVar . flip index renamedAppliedNames

  -- Build a map from constructor's argument name to its index
  let conArgIdxs = SortedMap.fromList $ mapI' con.args $ \idx, arg => (argName arg, idx)

  -- Determine indices of constructor's arguments that are given
  givenConArgs <- for givenConArgs.asList $ \givenArgNameStr => do
    let Just idx = lookup (UN $ Basic givenArgNameStr) conArgIdxs
      | Nothing => failAt conFC "INTERNAL ERROR: calculated given `\{givenArgNameStr}` is not found in an arguments list of the constructor"
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
  let fuelArg = "^cons_fuel^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
  pure $
    -- Happy case, given arguments conform out constructor's GADT indices
    [ callCanonic sig name (bindVar fuelArg) bindExprs .= deceqise !(consGenExpr sig con .| fromList givenConArgs .| varStr fuelArg) ]
    ++ if all isSimpleBindVar bindExprs then [] {- do not produce dead code if the happy case handles everything already -} else
      -- The rest case, if given arguments do not conform to the current constructor then return empty generator
      [ callCanonic sig name implicitTrue (replicate _ implicitTrue) .= `(empty) ]
