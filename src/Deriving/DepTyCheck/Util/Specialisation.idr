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

import public Data.Hashable
import public Data.Hashable.Base

%default total

record AllApps where
  constructor MkAllApps
  explicitArgs : List TTImp
  autoArgs : List TTImp
  namedArgs : SortedMap Name TTImp

addApp' : AnyApp -> AllApps -> AllApps
addApp' (PosApp s) = {explicitArgs $= (s ::)}
addApp' (NamedApp nm s) = {namedArgs $= insert nm s}
addApp' (AutoApp s) = {autoArgs $= (s ::)}
addApp' (WithApp s) = {explicitArgs $= (s ::)}

mkAllApps : List AnyApp -> AllApps
mkAllApps laa = foldl (flip addApp') (MkAllApps [] [] empty) $ reverse laa

getNamed : Maybe Name -> AllApps -> (Maybe TTImp, AllApps)
getNamed Nothing ap = (Nothing, ap)
getNamed (Just x) ap =
  case lookup x ap.namedArgs of
    Nothing => (Nothing, ap)
    Just t => (Just t, {namedArgs $= delete x} ap)

getGiven : Arg -> AllApps -> (Maybe TTImp, AllApps)
getGiven (MkArg _ ImplicitArg name _) ap = getNamed name ap
getGiven (MkArg _ ExplicitArg name _) (MkAllApps (x :: xs) autoArgs namedArgs) = (Just x, MkAllApps xs autoArgs namedArgs)
getGiven (MkArg _ ExplicitArg name _) ap = getNamed name ap
getGiven (MkArg _ AutoImplicit name _) (MkAllApps explicitArgs (x :: xs) namedArgs) = (Just x, MkAllApps explicitArgs xs namedArgs)
getGiven (MkArg _ AutoImplicit name _) ap = getNamed name ap
getGiven (MkArg _ (DefImplicit x) Nothing _) ap = (Just x, ap)
getGiven (MkArg _ (DefImplicit x) (Just n) _) ap =
  case lookup n ap.namedArgs of
    Nothing => (Just x, ap)
    Just t => (Just t , {namedArgs $= delete n} ap)

getGivens : List Arg -> AllApps -> List (Maybe TTImp)
getGivens [] aa = []
getGivens (x :: xs) aa = do
  let (mr, aa) = getGiven x aa
  mr :: getGivens xs aa

export
getGivens' : NamesInfoInTypes => TTImp -> Maybe (List (Arg, Maybe TTImp))
getGivens' t = do
  let (IVar _ tyName, aTerms) = unAppAny t
    | _ => Nothing
  let Just tyInfo = lookupType tyName
    | _ => Nothing
  Just $ zip tyInfo.args $ getGivens tyInfo.args (mkAllApps aTerms)


allQImpl : Monad m => TTImp -> m TTImp -> m TTImp
allQImpl pi@(IPi _ _ _ _ _ _) r = r
allQImpl _ _ = pure `(?)

allQuestions : TTImp -> TTImp
allQuestions t = runIdentity $ mapATTImp' allQImpl t

singleArg : Arg -> Nat -> Maybe TTImp -> (TTImp, List (Arg, Maybe TTImp))
singleArg a n v = do
  let n : Name = fromString "lam^\{show n}"
  (IVar EmptyFC n, [(MkArg a.count a.piInfo (Just n) $ allQuestions a.type, v)])

processArg : MonadLog m => NamesInfoInTypes => Nat -> Arg -> Maybe TTImp -> m (TTImp, List (Arg, Maybe TTImp))

processArgs' : MonadLog m => NamesInfoInTypes => Nat -> List (Arg, Maybe TTImp) -> m (List AnyApp, List (Arg, Maybe TTImp))
processArgs' k [] = pure ([], [])
processArgs' k ((x, y) :: xs) = do
  (aT, l) <- assert_total $ processArg k x y
  (recAA, l') <- processArgs' (k + length l) xs
  pure (appArg x aT :: recAA, l ++ l')

processArg argIdx arg Nothing = do
  -- logPoint DetailedDebug "deptycheck.util.specialisation.processArg" [] "Processing non-given \{show arg.name}"
  pure $ singleArg arg argIdx Nothing
processArg argIdx arg (Just x) = do
  -- logPoint DetailedDebug "deptycheck.util.specialisation.processArg" [] "Processing \{show arg.name} = \{show x}"
  let (appLhs, appTerms) = unAppAny x
  case getGivens' x of
    Just givens => map (mapFst $ reAppAny appLhs) $ processArgs' argIdx $ takeWhile (isJust . snd) givens
    _ => pure $ singleArg arg argIdx (Just x)

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
  map (bimap (reAppAny $ IVar EmptyFC sig.targetType.name) unzip) $
    processArgs' 0 $ mkArgs sig args givens

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

specTaskToName : TTImp -> Name
specTaskToName t = do
  let (_, lamBody) = unLambda t
  let (callee, _) = unAppAny lamBody
  let vname =
    case callee of
         (IVar _ n) => show $ snd $ unNS n
         x => show x
  fromString "\{vname}^\{show $ hash t}"

-- Using the monadic trick makes the performance *much* better.
specTaskToName' : Monad m => TTImp -> m Name
specTaskToName' t = do
  let (_, lamBody) = unLambda t
  let (callee, _) = unAppAny lamBody
  let vname =
    case callee of
         (IVar _ n) => show $ snd $ unNS n
         x => show x
  hash <- pure $ show $ hash t
  pure $ fromString "\{vname}^\{hash}.\{vname}^\{hash}"

nameUnambigAndVis : Elaboration m => Name -> m Bool
nameUnambigAndVis n = do
  [(_, vis)] <- getVis n
    | _ => pure False
  pure $ vis /= Private

allConstructorsVisible : Elaboration m => TypeInfo -> m Bool
allConstructorsVisible ti = do
  all id <$> traverse nameUnambigAndVis (name <$> ti.cons)

export %tcinline
specialiseIfNeeded :
  Elaboration m =>
  NamesInfoInTypes =>
  DerivationClosure m =>
  (sig : GenSignature) ->
  (fuel : TTImp) ->
  Vect sig.givenParams.size TTImp ->
  m $ Maybe (List Decl, TypeInfo, TTImp)
specialiseIfNeeded sig fuel givenParamValues = do
  -- Check if there are any given type args, if not return Nothing
  let True = any (\a => snd (unPi a.type) == `(Type)) $ index' sig.targetType.args <$> Prelude.toList sig.givenParams
    | False => pure Nothing
  True <- allConstructorsVisible sig.targetType
    | False => pure Nothing
  let givenIdxVals = Prelude.toList sig.givenParams `zipV` givenParamValues
  (lambdaRet, fvArgs, givenSubst) <- processArgs sig (withIndex sig.targetType.args) givenIdxVals
  let preNorm = foldr lam lambdaRet fvArgs
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Task before normalisation: \{show preNorm}"
  (lambdaTy, lambdaBody) <- normaliseTask fvArgs lambdaRet
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "NormaliseTask returned: lambdaTy = \{show lambdaTy};"
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "                        lambdaBody = \{show lambdaBody};"
  specName <- specTaskToName' lambdaBody
  logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Specialised type name: \{show specName}"
  (specTy, specDecls) : (TypeInfo, List Decl) <- case lookupType specName of
    Nothing => do
      info <- try (Just <$> getInfo' specName) (pure Nothing)
      case info of
        Nothing => do
          logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Specialised type not found, deriving..."
          Right (specTy, specDecls) <- runEitherT {m} {e=SpecialisationError} $ specialiseDataRaw specName lambdaTy lambdaBody
            | Left err => fail "INTERNAL ERROR: Specialisation \{show lambdaBody} failed with error \{show err}."
          logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Derived \{show specTy.name}"
          declare specDecls
          pure (specTy, [])
        Just specTy => do
          logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Found \{show specTy.name}"
          pure (specTy, [])    
    Just specTy => do
      logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Found \{show specTy.name}"
      pure (specTy, [])
  -- logPoint DetailedDebug "deptycheck.util.specialisation" [sig] "Found or derived \{show specTy.name}"
  let Yes stNamed = areAllTyArgsNamed specTy
    | No _ => fail "INTERNAL ERROR: Specialised type \{show specTy.name} does not have fully named arguments and constructors."
  let (newGP ** newGVals) = genGivens $ mapMaybe (\(a,b) => map (,b) a) $ zip givenSubst $ withIndex specTy.args
  (inv, cg_rhs) <- callGen (MkGenSignature specTy newGP) fuel newGVals
  let inv = case cg_rhs of
        Nothing => inv
        Just (n ** perm) => reorderGend False perm inv
  pure $ Just (specDecls, specTy, inv)
