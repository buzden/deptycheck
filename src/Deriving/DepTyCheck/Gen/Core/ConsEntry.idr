||| Derivation of the outer layer of a constructor-generating function, performing GADT indices check of given arguments.
module Deriving.DepTyCheck.Gen.Core.ConsEntry

import public Control.Monad.State.Tuple

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.Core.ConsDerive
import public Deriving.DepTyCheck.Gen.Core.Util

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

  -- Normalise the types in constructor; expand functions that are used as types, if possible
  con <- normaliseCon con

  -- Acquire constructor's return type arguments
  let (conRetTy, conRetTypeArgs) = unAppAny con.type
  let conRetTypeArgs = conRetTypeArgs <&> getExpr

  -- Match lengths of `conRetTypeArgs` and `sig.targetType.args`
  let Yes conRetTypeArgsLengthCorrect = conRetTypeArgs.length `decEq` sig.targetType.args.length
    | No _ => failAt conFC "INTERNAL ERROR: length of the return type does not equal to the type's arguments count"

  let conRetTypeArg : Fin sig.targetType.args.length -> TTImp
      conRetTypeArg idx = index' conRetTypeArgs $ rewrite conRetTypeArgsLengthCorrect in idx

  -- Determine names of the arguments of the constructor (as a function)
  let conArgNames = fromList $ argName <$> con.args

  -- For given arguments, determine whether they are
  --   - just a free name
  --   - repeated name of another given parameter (need of `decEq`)
  --   - (maybe, deeply) constructor call (need to match)
  --   - function call on a free param (need to use "inverted function" filtering trick)
  --   - something else (cannot manage yet)
  deepConsApps <- for sig.givenParams.asVect $ \idx => do
    let argExpr = conRetTypeArg idx
    let Right analysed = analyseDeepConsApp True conArgNames argExpr
      | Left err => failAt conFC "Argument #\{show idx} is not supported yet, argument expression: \{show argExpr}, reason: \{err}"
    pure analysed

  -- Acquire LHS bind expressions for the given parameters
  -- Determine pairs of names which should be `decEq`'ed
  let getAndInc : forall m. MonadState Nat m => m Nat
      getAndInc = get <* modify S
  ((givenConArgs, decEqedNames, _), bindExprs) <-
    runStateT (empty, empty, 0) {stateType=(SortedSet Name, SortedSet (String, String), Nat)} {m} $
      for deepConsApps $ \(appliedNames ** bindExprF) => do
        renamedAppliedNames <- for appliedNames.asVect $ \(name, typeDetermined) => do
          let bindName = bindNameRenamer name
          if cast typeDetermined
            then pure $ const implicitTrue -- no need to match type-determined parameter by hand
            else if contains name !get
            then do
              -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
              let substName = "to_be_deceqed^^" ++ bindName ++ show !getAndInc
              modify $ insert (bindName, substName)
              pure $ \alreadyMatchedRenames => bindVar $ if contains substName alreadyMatchedRenames then bindName else substName
            else modify (insert name) $> const (bindVar bindName)
        let _ : Vect appliedNames.length $ SortedSet String -> TTImp = renamedAppliedNames
        pure $ \alreadyMatchedRenames => bindExprF $ \idx => index idx renamedAppliedNames $ alreadyMatchedRenames
  let bindExprs = \alreadyMatchedRenames => bindExprs <&> \f => f alreadyMatchedRenames

  -- Build a map from constructor's argument name to its index
  let conArgIdxs = SortedMap.fromList $ mapI con.args $ \idx, arg => (argName arg, idx)

  -- Determine indices of constructor's arguments that are given
  givenConArgs <- for givenConArgs.asList $ \givenArgName => do
    let Just idx = lookup givenArgName conArgIdxs
      | Nothing => failAt conFC "INTERNAL ERROR: calculated given `\{show givenArgName}` is not found in an arguments list of the constructor"
    pure idx

  -- Equalise index values which must be propositionally equal to some parameters
  -- NOTE: Here I do all `decEq`s in a row and then match them all against `Yes`.
  --       I could do this step by step and this could be more effective in large series.
  let deceqise : (lhs : Vect sig.givenParams.asList.length TTImp -> TTImp) -> (rhs : TTImp) -> Clause
      deceqise lhs rhs = step lhs empty $ orderLikeInCon decEqedNames where

        step : (withlhs : Vect sig.givenParams.asList.length TTImp -> TTImp) ->
               (alreadyMatchedRenames : SortedSet String) ->
               (left : List (String, String)) ->
               Clause
        step withlhs matched [] = PatClause EmptyFC .| withlhs (bindExprs matched) .| rhs
        step withlhs matched ((orig, renam)::rest) =
          WithClause EmptyFC (withlhs $ bindExprs matched) MW
            `(Decidable.Equality.decEq ~(varStr renam) ~(varStr orig))
            Nothing []
            [ -- happy case
              step ((.$ `(Prelude.Yes Builtin.Refl)) . withlhs) (insert renam matched) rest
            , -- empty case
              PatClause EmptyFC .| withlhs (bindExprs matched) .$ `(Prelude.No _) .| `(empty)
            ]

        -- Order pairs by the first element like they are present in the constructor's signature
        orderLikeInCon : Foldable f => f (String, String) -> List (String, String)
        orderLikeInCon = do
          let conArgStrNames = mapMaybe argStrName con.args
          let conNameToIdx : SortedMap _ $ Fin conArgStrNames.length := fromList $ mapI conArgStrNames $ flip (,)
          let [AsInCon] Ord (String, String) where
                compare (origL, renL) (origR, renR) = comparing (lookup' conNameToIdx) origL origR <+> compare renL renR
          SortedSet.toList . foldl insert' (empty @{AsInCon})
          where
            argStrName : Arg -> Maybe String
            argStrName $ MkArg {name=Just $ UN (Basic n), _} = Just n
            argStrName _                                     = Nothing

  -- Form the declaration cases of a function generating values of particular constructor
  let fuelArg = "^cons_fuel^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
  pure $
    -- Happy case, given arguments conform out constructor's GADT indices
    [ deceqise (callCanonic sig name $ bindVar fuelArg) !(consGenExpr sig con .| fromList givenConArgs .| varStr fuelArg) ]
    ++ if all isSimpleBindVar $ bindExprs SortedSet.empty then [] {- do not produce dead code if the happy case handles everything already -} else
      -- The rest case, if given arguments do not conform to the current constructor then return empty generator
      [ callCanonic sig name implicitTrue (replicate _ implicitTrue) .= `(empty) ]
