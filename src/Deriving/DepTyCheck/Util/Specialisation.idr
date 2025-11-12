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

isSimpleN : Name -> Bool
isSimpleN (UN (Basic str)) = (fst $ span isLower str) /= ""
isSimpleN _ = False

||| Given an argument, a possible given value for it, and a set of free variable names in scope,
||| return argument value in the specialisation lambda body,
||| as well as a list of newly introduced free variables and their given values
processArg : Arg -> Maybe TTImp -> SortedSet Name -> (TTImp, List (Arg, Maybe TTImp))
processArg arg Nothing fvNames = (IVar EmptyFC $ fromMaybe "_" arg.name, [(arg, Nothing)])
processArg arg (Just given) fvNames =
  case snd $ unPi arg.type of
    `(Type) => do
      let simpleNames = filter isSimpleN $ allVarNames given
      let newNames = filter (not . contains' fvNames) simpleNames
      let newArgs : List (Arg, Maybe TTImp) = newNames <&> \x => (MkArg MW ExplicitArg (Just x) `(_), Just $ IVar EmptyFC x)
      (given, newArgs)
    _ => (IVar EmptyFC $ fromMaybe "_" arg.name, [(arg, Just given)])

processArgs' :
  List (Fin x, Arg) ->
  List (Fin x, TTImp) ->
  SnocList (Arg, Maybe TTImp) ->
  SortedSet Name ->
  (List AnyApp, SnocList (Arg, Maybe TTImp), SortedSet Name)
processArgs' [] _ fvArgs fvNames = ([], fvArgs, fvNames)
processArgs' ((argIdx, arg) :: xs) givens fvArgs fvNames = do
  let (givens, argVal, newFVs) : (List _, TTImp, List _) = case givens of
        [] => ([], processArg arg Nothing fvNames)
        (givenIdx, givenVal) :: ys =>
          if givenIdx == argIdx
            then (ys, processArg arg (Just givenVal) fvNames)
            else (givens, processArg arg Nothing fvNames)
  let newFVNames = SortedSet.fromList $ fromMaybe "_" . name . fst <$> newFVs
  let fvArgs = fvArgs <>< newFVs
  let fvNames = union fvNames newFVNames
  mapFst (appArg arg argVal ::) $ processArgs' xs givens fvArgs fvNames

processArgs :
  (sig : GenSignature) ->
  List (Fin sig.targetType.args.length, Arg) ->
  List (Fin sig.targetType.args.length, TTImp) ->
  (TTImp, List Arg, List $ Maybe TTImp)
processArgs sig args givens = do
  let (argVals, fvArgs, _) = processArgs' args givens [<] empty
  (reAppAny (IVar EmptyFC sig.targetType.name) argVals, unzip $ toList fvArgs)

remap : List (Maybe TTImp, Fin x, Arg) -> List (TTImp, Fin x, Arg)
remap [] = []
remap ((Nothing, _, _) :: xs) = remap xs
remap ((Just x, y, z) :: xs) = (x,y,z) :: remap xs

formGivenVals : Vect l _ -> List TTImp -> Vect l TTImp
formGivenVals [] _ = []
formGivenVals (_ :: xs) [] = (`(_) :: formGivenVals xs [])
formGivenVals (x :: xs) (y :: ys) = y :: formGivenVals xs ys

genSS : List (TTImp, Fin x, Arg) -> (s : SortedSet (Fin x) ** Vect s.size TTImp)
genSS l = do
  let (l1, l2) = unzip l
  let (l2, l3) = unzip l2
  let s = SortedSet.fromList l2
  let gv = formGivenVals (Vect.fromList $ Prelude.toList s) l1
  (s ** gv)

%tcinline
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
  let givenIdxVals = (Prelude.toList sig.givenParams) `zipV` givenParamValues
  let (lambdaRet, fvArgs, givenSubst) = processArgs sig (withIndex sig.targetType.args) givenIdxVals
  (lambdaTy, lambdaBody) <- normaliseTask fvArgs lambdaRet
  let specName = specTaskToName lambdaBody
  (specTy, specDecls) : (TypeInfo, List Decl) <- case lookupType specName of
    Nothing => do
      Right (specTy, specDecls) <- runEitherT {m} {e=SpecialisationError} $ specialiseDataRaw specName lambdaTy lambdaBody
      | Left err => fail "INTERNAL ERROR: Specialisation \{show lambdaBody} failed with error \{show err}."
      pure (specTy, specDecls)
    Just specTy => pure (specTy, [])
  let Yes stNamed = areAllTyArgsNamed specTy
    | No _ => fail "INTERNAL ERROR: Specialised type \{show specTy.name} does not have fully named arguments and constructors."
  let (newGP ** newGVals) = genSS $ remap $ zip givenSubst $ withIndex specTy.args
  (inv, cg_rhs) <- callGen (MkGenSignature specTy newGP) fuel newGVals
  let inv = case cg_rhs of
        Nothing => inv
        Just (n ** perm) => reorderGend False perm inv
  pure $ Just (specDecls, specTy, inv)
