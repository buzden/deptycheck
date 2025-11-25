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

||| Given an argument, a possible given value for it, and a set of free variable names in scope,
||| return argument value in the specialisation lambda body,
||| as well as a list of newly introduced free variables and their given values
processArg : NamesInfoInTypes => Subset Arg IsNamedArg -> Maybe TTImp -> SortedSet Name -> (TTImp, List (Subset Arg IsNamedArg, Maybe TTImp))
processArg (Element arg argN) Nothing fvNames = do
  let arg' : Arg
      arg' = MkArg arg.count arg.piInfo (Just $ fromString $ "pt^\{show $ argName arg}") arg.type
  (IVar EmptyFC $ argName arg', [(Element arg' ItIsNamed, Nothing)])
processArg (Element arg argN) (Just given) fvNames =
  case snd $ unPi arg.type of
    IType _ => do
      let simpleNames = filter (isNothing . lookupType) $ allVarNames given
      let newNames    = filter (not . contains' fvNames) simpleNames
      let newArgs : List (Subset Arg IsNamedArg, Maybe TTImp) = do
        newNames <&> \x =>(Element (MkArg MW ExplicitArg (Just x) `(_)) ItIsNamed, Just $ IVar EmptyFC x)
          -- let x = fromString "at<\{show $ argName arg}>^\{show x}"
          -- in (Element (MkArg MW ExplicitArg (Just x) `(_)) ItIsNamed, Just $ IVar EmptyFC x)
      (given, newArgs)
    _ => do
      let arg' : Arg
          arg' = MkArg arg.count arg.piInfo (Just $ fromString $ "pt^\{show $ argName arg}") arg.type
      (IVar EmptyFC $ argName arg', [(Element arg' ItIsNamed, Just given)])

processArgs' :
  NamesInfoInTypes =>
  List (Fin x, Subset Arg IsNamedArg) ->
  List (Fin x, TTImp) ->
  SnocList (Arg, Maybe TTImp) ->
  SortedSet Name ->
  (List AnyApp, SnocList (Arg, Maybe TTImp), SortedSet Name)
processArgs' [] _ fvArgs fvNames = ([], fvArgs, fvNames)
processArgs' ((argIdx, arg) :: xs) givens fvArgs fvNames = do
  let (givens, argVal, newFVs) : (List _, TTImp, List (Subset Arg IsNamedArg, Maybe TTImp)) =
    case givens of
        [] => ([], processArg arg Nothing fvNames)
        (givenIdx, givenVal) :: ys =>
          if givenIdx == argIdx
            then (ys    , processArg arg (Just givenVal) fvNames)
            else (givens, processArg arg Nothing         fvNames)
  let newFVNames = SortedSet.fromList $ (\(Element a _) : Subset Arg IsNamedArg => argName a) . Builtin.fst <$> newFVs
  let fvArgs = fvArgs <>< map (mapFst fst) newFVs
  let fvNames = union fvNames newFVNames
  mapFst (appArg (fst arg) argVal ::) $ processArgs' xs givens fvArgs fvNames

processArgs :
  NamesInfoInTypes =>
  (sig : GenSignature) ->
  List (Fin sig.targetType.args.length, Subset Arg IsNamedArg) ->
  List (Fin sig.targetType.args.length, TTImp) ->
  (TTImp, List Arg, List $ Maybe TTImp)
processArgs sig args givens = do
  let (argVals, fvArgs, _) = processArgs' args givens [<] empty
  (reAppAny (IVar EmptyFC sig.targetType.name) argVals, unzip $ toList fvArgs)

export
formGivenVals : Vect l _ -> List TTImp -> Vect l TTImp
formGivenVals []        _         = []
formGivenVals (_ :: xs) []        = `(_) :: formGivenVals xs []
formGivenVals (x :: xs) (y :: ys) = y    :: formGivenVals xs ys

genSS : List (TTImp, Fin x, Arg) -> (s : SortedSet (Fin x) ** Vect s.size TTImp)
genSS l = do
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
  let argsWithPrf = pushIn sig.targetType.args sig.targetTypeCorrect.tyArgsNamed
  let givenIdxVals = Prelude.toList sig.givenParams `zipV` givenParamValues
  let (lambdaRet, fvArgs, givenSubst) = processArgs sig (zip (List.allFins sig.targetType.args.length) argsWithPrf) givenIdxVals
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
  let (newGP ** newGVals) = genSS $ mapMaybe (\(a,b) => map (,b) a) $ zip givenSubst $ withIndex specTy.args
  (inv, cg_rhs) <- callGen (MkGenSignature specTy newGP) fuel newGVals
  let inv = case cg_rhs of
        Nothing => inv
        Just (n ** perm) => reorderGend False perm inv
  pure $ Just (specDecls, specTy, inv)
