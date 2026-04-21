||| Derivation of the outer layer of a constructor-generating function, performing GADT indices check of given arguments.
module Deriving.DepTyCheck.Gen.ForOneTypeCon.Impl

import public Control.Monad.Error.Either
import public Control.Monad.State
import public Control.Monad.State.Tuple
import public Control.Monad.Writer

import public Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Interface
import public Deriving.DepTyCheck.Util.DeepConsApp

%default total

-------------------------------------------------
--- Derivation of a generator for constructor ---
-------------------------------------------------

isSimpleBindVar : TTImp -> Bool
isSimpleBindVar $ IBindVar {} = True
isSimpleBindVar _             = False

export
canonicConsBody : DeriveBodyRhsForCon => DerivationClosure m => Elaboration m => NamesInfoInTypes => ConsRecs =>
                  GenSignature -> Name -> Con -> m $ List Clause
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
  let conArgNames = fromList $ argName' <$> con.args

  -- For given arguments, determine whether they are
  --   - just a free name
  --   - repeated name of another given parameter (need for `decEq`)
  --   - (maybe, deeply) constructor call (need to match)
  --   - a function call to a determined arg (can be calculated, thus need for `decEq`)
  --   - a function call on a free param (thus, need to use "inverted function" filtering trick; not supported now)
  --   - something else (cannot manage yet, unless it is fully determined by other given arguments)
  deepConsApps : Vect _ $ DeepConsAnalysisRes True <- for sig.givenParams.asVect $ \idx => do
    let argExpr = conRetTypeArg idx
    let (fns, errs) = runWriter {w=List String} $ analyseDeepConsApp True conArgNames argExpr
    when (not $ null errs) $ failAt conFC $
      "Argument #\{show idx} of \{show con.name} with given type arguments [\{showGivens sig}] is not supported, " ++
      "argument expression: \{show argExpr}, reason(s): \{joinBy "; " errs}"
    pure fns
  let allAppliedFreeNames = foldMap (SortedSet.fromList . map fst . fst) deepConsApps
  let badDecEqExpr : ConsDetermInfo -> Maybe TTImp
      badDecEqExpr (MustDecEqWith e) = whenT (not $ null $ (allVarNames' e `intersection` conArgNames) `difference` allAppliedFreeNames) e
      badDecEqExpr _                 = Nothing
  for_ deepConsApps $ \(vs ** _) => whenJust (foldAlt' vs $ badDecEqExpr . snd) $ \e => failAt conFC $
    "Unsupported constructor \{show con.name} with given type arguments [\{showGivens sig}] since it contains " ++
    "an undetermined non-constructor expression `\{show e}` as a given"

  -- Acquire LHS bind expressions for the given parameters
  -- Determine pairs of names which should be `decEq`'ed
  let getAndInc : forall m. MonadState Nat m => m Nat
      getAndInc = get <* modify S
  let deceqedName : forall m. MonadState Nat m => Name -> m Name
      -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
      deceqedName name = pure $ UN $ Basic $ "to_be_deceqed^^" ++ show name ++ show !getAndInc
  ((givenConArgs, decEqedNames, _), bindExprs) <-
    runStateT (empty, [], 0) {stateType=(SortedSet Name, List (Either TTImp Name, Name), Nat)} {m} $
      for deepConsApps $ \(appliedNames ** bindExprF) => do
        renamedAppliedNames <- for appliedNames.asVect $ \(name, typeDetermined) =>
          case typeDetermined of
            DeterminedByType => pure $ const implicitTrue -- no need to match type-determined parameter by hand
            NotDeterminedByType => if SortedSet.contains name !get
              then do
                substName <- deceqedName name
                modify $ (::) (Right name, substName)
                pure $ \alreadyMatchedRenames => bindVar $ if contains substName alreadyMatchedRenames then name else substName
              else modify (SortedSet.insert name) $> const (bindVar name)
            MustDecEqWith e => do
              substName <- deceqedName name
              modify $ (::) (Left e, substName)
              pure $ \alreadyMatchedRenames => if contains substName alreadyMatchedRenames then {- e -} implicitTrue else bindVar substName
        let _ : Vect appliedNames.length $ SortedSet Name -> TTImp = renamedAppliedNames
        pure $ \alreadyMatchedRenames => bindExprF $ \idx => index idx renamedAppliedNames $ alreadyMatchedRenames
  let bindExprs = \alreadyMatchedRenames => bindExprs <&> \f => f alreadyMatchedRenames

  -- Build a map from constructor's argument name to its index
  let conArgIdxs = SortedMap.fromList $ mapI con.args $ \idx, arg => (argName' arg, idx)

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
               (alreadyMatchedRenames : SortedSet Name) ->
               (left : List (Either TTImp Name, Name)) ->
               Clause
        step withlhs matched [] = PatClause EmptyFC .| withlhs (bindExprs matched) .| rhs
        step withlhs matched ((orig, renam)::rest) =
          WithClause EmptyFC (withlhs $ bindExprs matched) MW
            `(Decidable.Equality.decEq ~(var renam) ~(either id var orig))
            Nothing []
            [ -- happy case
              step ((.$ `(Prelude.Yes Builtin.Refl)) . withlhs) (insert renam matched) rest
            , -- empty case
              PatClause EmptyFC .| withlhs (bindExprs matched) .$ `(Prelude.No _) .| `(empty)
            ]

        -- Order pairs by the first element like they are present in the constructor's signature
        orderLikeInCon : Foldable f => f (Either TTImp Name, Name) -> List (Either TTImp Name, Name)
        orderLikeInCon = do
          let conArgNames = mapMaybe Arg.name con.args
          let conNameToIdx : SortedMap _ $ Fin conArgNames.length := fromList $ mapI conArgNames $ flip (,)
          let [AsInCon] Ord (Either TTImp Name, Name) where
                compare (Left _, _) (Right _, _) = LT
                compare (Right _, _) (Left _, _) = GT
                compare (Right origL, renL) (Right origR, renR) = comparing (lookup' conNameToIdx) origL origR <+> compare renL renR
                compare (Left _, renL) (Left _, renR) = compare renL renR
          Prelude.toList . foldl SortedSet.insert' (empty @{AsInCon})

  -- Form the declaration cases of a function generating values of particular constructor
  let fuelArg = "^cons_fuel^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
  pure $
    -- Happy case, given arguments conform out constructor's GADT indices
    [ deceqise (callCanonic sig name $ bindVar fuelArg) !(consGenExpr sig con .| fromList givenConArgs .| var fuelArg) ]
    ++ if all isSimpleBindVar $ bindExprs SortedSet.empty then [] {- do not produce dead code if the happy case handles everything already -} else
      -- The rest case, if given arguments do not conform to the current constructor then return empty generator
      [ callCanonic sig name implicitTrue (replicate _ implicitTrue) .= `(empty) ]
