module Deriving.DepTyCheck.Util.Specialisation

import public Control.Monad.Either

import public Data.DPair
import public Data.List.Ex
import public Data.List.Map
import public Data.SortedMap
import public Data.SortedMap.Extra
import public Data.SortedSet

import public Deriving.DepTyCheck.Gen.ForOneType.Interface

import public Deriving.SpecialiseData
import public Language.Reflection.Unify

%default total

allQImpl : Monad m => TTImp -> m TTImp -> m TTImp
allQImpl pi@(IPi _ _ _ _ _ _) r = r
allQImpl _ _ = pure `(?)

allQuestions : TTImp -> TTImp
allQuestions t = runIdentity $ mapATTImp' allQImpl t

singleArg : Arg -> Nat -> Maybe TTImp -> (TTImp, List (Arg, Maybe TTImp))
singleArg a n v = do
  let n : Name = fromString "lam^\{show n}"
  (IVar EmptyFC n, [(MkArg a.count a.piInfo (Just n) $ allQuestions a.type, v)])

processArg : MonadLog m => NamesInfoInTypes => Arg -> Maybe TTImp -> Nat -> m (TTImp, List (Arg, Maybe TTImp))

processArgs' : MonadLog m => NamesInfoInTypes => List Arg -> List (Maybe TTImp) -> Nat -> m (List AnyApp, List (Arg, Maybe TTImp))
processArgs' [] mss k = pure ([], [])
processArgs' (x :: xs) [] k = pure ([], [])
processArgs' (x :: xs) (y :: ys) k = do
  (aT, l) <- assert_total $ processArg x y k
  (recAA, l') <- processArgs' xs ys (k + length l)
  pure (appArg x aT :: recAA, l ++ l')

processArg arg Nothing argIdx = do
  -- logPoint DetailedDebug "deptycheck.util.specialisation.processArg" [] "Processing non-given \{show arg.name}"
  pure $ singleArg arg argIdx Nothing
processArg arg (Just x) argIdx = do
  -- logPoint DetailedDebug "deptycheck.util.specialisation.processArg" [] "Processing \{show arg.name} = \{show x}"
  let (appLhs, appTerms) = unAppAny x
  case (snd $ unPi arg.type, appLhs) of
    (IType _, IVar _ tyName) => case lookupType tyName of
      Just tyInfo => do
        map (mapFst (reAppAny appLhs)) $ processArgs' tyInfo.args (map (Just . getExpr) appTerms) argIdx
      _ => do
        -- logPoint DetailedDebug "deptycheck.util.specialisation.processArg" [] "Can't find type \{show tyName}"
        pure $ singleArg arg argIdx (Just x)
    _ => do
      -- logPoint DetailedDebug "deptycheck.util.specialisation.processArg" [] "Either non-type arg or wrong appLhs: \{show arg.type}; \{show appLhs}"
      pure $ singleArg arg argIdx (Just x)

mkArgs :
  NamesInfoInTypes =>
  (sig : GenSignature) ->
  List (Fin sig.targetType.args.length, Arg) ->
  List (Fin sig.targetType.args.length, TTImp) ->
  List (Arg, Maybe TTImp)
mkArgs sig [] _ = []
mkArgs sig ((_, x) :: xs) [] = (x, Nothing) :: mkArgs sig xs []
mkArgs sig ((i1, x) :: xs) g@((i2, y) :: ys) =
  if i1 == i2
    then (x, Just y) :: mkArgs sig xs ys
    else (x, Nothing) :: mkArgs sig xs g

processArgs :
  MonadLog m =>
  NamesInfoInTypes =>
  (sig : GenSignature) ->
  List (Fin sig.targetType.args.length, Arg) ->
  List (Fin sig.targetType.args.length, TTImp) ->
  m (TTImp, List Arg, List $ Maybe TTImp)
processArgs sig args givens = do
  let (args', givens') = unzip $ mkArgs sig args givens
  (argVals, fvArgs) <- processArgs' args' givens' 0
  pure (reAppAny (IVar EmptyFC sig.targetType.name) argVals, unzip fvArgs)

export
formGivenVals : Vect l _ -> List TTImp -> Vect l TTImp
formGivenVals []        _         = []
formGivenVals (_ :: xs) []        = `(_) :: formGivenVals xs []
formGivenVals (x :: xs) (y :: ys) = y    :: formGivenVals xs ys

genGivens : List (TTImp, Fin x, Arg) -> (s : SortedSet (Fin x) ** Vect s.size TTImp)
genGivens l = do
  let (l1, l2, l3) = unzip3 l
  let s = SortedSet.fromList l2
  let gv = formGivenVals (Vect.fromList $ Prelude.toList s) l1
  (s ** gv)

export %tcinline
specialiseIfNeeded :
  Monad m =>
  Elaboration m =>
  NamesInfoInTypes =>
  DerivationClosure m =>
  (sig : GenSignature) ->
  (specTaskToName : TTImp -> Name) ->
  (fuel : TTImp) ->
  Vect sig.givenParams.size TTImp ->
  m $ Maybe (List Decl, TypeInfo, TTImp)
specialiseIfNeeded sig specTaskToName fuel givenParamValues = do
  -- Check if there are any given type args, if not return Nothing
  let True = any (\a => snd (unPi a.type) == `(Type)) $ index' sig.targetType.args <$> Prelude.toList sig.givenParams
    | False => pure Nothing
  let givenIdxVals = Prelude.toList sig.givenParams `zipV` givenParamValues
  (lambdaRet, fvArgs, givenSubst) <- processArgs sig (withIndex sig.targetType.args) givenIdxVals
  let preNorm = foldr lam lambdaRet fvArgs
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Task before normalisation: \{show preNorm}"
  (lambdaTy, lambdaBody) <- normaliseTask fvArgs lambdaRet
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "NormaliseTask returned: lambdaTy = \{show lambdaTy};"
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "                        lambdaBody = \{show lambdaBody};"
  let specName = specTaskToName lambdaBody
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Specialised type name: \{show specName}"
  (specTy, specDecls) : (TypeInfo, List Decl) <- case lookupType specName of
    Nothing => do
      logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Specialised type not found, deriving..."
      Right (specTy, specDecls) <- runEitherT {m} {e=SpecialisationError} $ specialiseDataRaw specName lambdaTy lambdaBody
      | Left err => fail "INTERNAL ERROR: Specialisation \{show lambdaBody} failed with error \{show err}."
      pure (specTy, specDecls)
    Just specTy => pure (specTy, [])
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Found or derived \{show specTy.name}"
  let Yes stNamed = areAllTyArgsNamed specTy
    | No _ => fail "INTERNAL ERROR: Specialised type \{show specTy.name} does not have fully named arguments and constructors."
  let (newGP ** newGVals) = genGivens $ mapMaybe (\(a,b) => map (,b) a) $ zip givenSubst $ withIndex specTy.args
  (inv, cg_rhs) <- callGen (MkGenSignature specTy newGP) fuel newGVals
  let inv = case cg_rhs of
        Nothing => inv
        Just (n ** perm) => reorderGend False perm inv
  pure $ Just (specDecls, specTy, inv)
