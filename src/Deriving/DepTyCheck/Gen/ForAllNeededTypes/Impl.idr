||| A bridge between a single act of derivation (for a single type) and a user derivation task
module Deriving.DepTyCheck.Gen.ForAllNeededTypes.Impl

import public Control.Monad.State

import public Data.DPair
import public Data.List.Set
import public Data.List.Ex
import public Data.List.Map
import public Data.SortedMap

import public Decidable.Equality

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
      let newArgs : List (Arg, Maybe TTImp) = (\x => (MkArg MW ExplicitArg (Just x) `(_), Just $ IVar EmptyFC x)) <$> newNames
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
        ((givenIdx, givenVal) :: ys) =>
          if (givenIdx == argIdx)
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


--- Particular implementations producing the-core-derivation-function closure ---

ClosuringContext : (Type -> Type) -> Type
ClosuringContext m =
  ( ListSet GenSignature                                                 -- gens already asked to be derived
  , MonadState  (ListSet GenSignature, ListSet GenSignature) m           -- two queues of gens to be derived, one for known types, one the unknown ones
  )

nameForGen : GenSignature -> Name
nameForGen sig = let (ty, givs) = characteristics sig in UN $ Basic $ "<\{ty}>\{show givs}"
-- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend.

-- Instead of staticaly ensuring that map holds only correct values, we check dynamically, because it's hard to go through `==`-based lookup of maps.
lookupLengthChecked : (intSig : GenSignature) -> SortedMap GenSignature (ExternalGenSignature, Name) ->
                      Maybe (Name, Subset ExternalGenSignature $ \extSig => extSig.givenParams.size = intSig.givenParams.size)
lookupLengthChecked intSig m = lookup intSig m >>= \(extSig, name) => (name,) <$>
                                 case decEq extSig.givenParams.size intSig.givenParams.size of
                                    Yes prf => Just $ Element extSig prf
                                    No _    => Nothing

deriveAll : NamesInfoInTypes => ConsRecs => (cc : ClosuringContext m) => DeriveBodyForType => DerivationClosure m => Elaboration m =>
            ListSet TypeInfo -> List (Decl, Decl) -> m (ListSet TypeInfo, List (Decl, Decl))
deriveAll weightFunTys decls {cc=(alreadyDerived, _)}= do
  (toDeriveKnown, toDeriveUnknown) <- mapHom ((`difference` alreadyDerived) . normalise) <$> get {stateType=(ListSet _, ListSet _)}
  put (empty, toDeriveUnknown)
  (weightFunTys, decls) <- bimap (foldl insert' weightFunTys . join) (decls ++) . unzip <$> for (toList toDeriveKnown) deriveOne
  if not $ null toDeriveKnown
    then assert_total $ deriveAll {cc=(alreadyDerived `union` toDeriveKnown, %search)} weightFunTys decls
    else if null toDeriveUnknown
      then pure (weightFunTys, decls)
      else do
        (niit, cr) <- updateNamesAndConsRecs $ targetType <$> toList toDeriveUnknown
        put (toDeriveUnknown, empty)
        assert_total $ deriveAll @{niit} @{cr} {cc=(alreadyDerived, %search)} weightFunTys decls
  where
    deriveOne : GenSignature -> m (List TypeInfo, Decl, Decl)
    deriveOne sig = do
      let name = nameForGen sig
      -- derive declaration and body for the asked signature. It's important to call it AFTER update of the map in the state to not to cycle
      let genFunClaim = export' name $ canonicSig sig
      (tyWithWeightFuns, genFunBody) <- logBounds Info "deptycheck.derive.type" [sig] $ canonicBody sig name
      pure (tyWithWeightFuns, genFunClaim, def name genFunBody)

DeriveBodyForType => ClosuringContext m => Elaboration m => SortedMap GenSignature (ExternalGenSignature, Name) => DerivationClosure m where

  callGen sig fuel values = do

    -- look for external gens, and call it if exists
    let Nothing = lookupLengthChecked sig %search
      | Just (name, Element extSig lenEq) =>
          logValue Details "deptycheck.derive.closuring.external" [sig] "is used as an external generator" $
            (callExternalGen extSig name (var outmostFuelArg) $ rewrite lenEq in values, Just (_ ** extSig.gendOrder))

    -- check if internal generator asked for is for a primitive type
    when (isTypeInfoPrim sig.targetType) $
      fail "Cannot derive generator for the primitive type \{show $ extractTargetTyExpr sig.targetType}, use external instead"

    -- remember the task to derive, if necessary
    when (not $ List.Set.contains sig %search) $ do
      modify $ if isTypeKnown sig.targetType then mapFst $ normalise . List.Set.insert sig else mapSnd $ normalise . List.Set.insert sig

    -- call the internal gen
    logValue DetailedDebug "deptycheck.derive.closuring.internal" [sig] "is used as an internal generator"
      (callCanonic sig (nameForGen sig) fuel values, Nothing)

--- Canonic-dischagring function ---

%hide Data.Vect.Dependent.(<*>)

declName : Decl -> String
declName $ IClaim $ MkFCVal _ $ MkIClaimData {type = MkTy {ty, _}, _} = show ty
declName $ IData _ _ _ $ MkData  {n, _} = show n
declName $ IData _ _ _ $ MkLater {n, _} = show n
declName $ IDef _ nm _ = show nm
declName $ IParameters _ _ [] = "P"
declName $ IParameters _ _ (d::_) = declName d
declName $ IRecord _ _ _ _ $ MkRecord {n, _} = show n
declName $ INamespace _ (MkNS ns) _ = joinBy "." $ reverse ns
declName $ ITransform _ nm _ _ = show nm
declName $ IRunElabDecl {} = "Z"
declName $ ILog {} = "Z"
declName $ IBuiltin _ _ nm = show nm

export
runCanonic : DeriveBodyForType => NamesInfoInTypes => ConsRecs =>
             SortedMap ExternalGenSignature Name -> (forall m. DerivationClosure m => m a) -> Elab (a, List Decl)
runCanonic exts calc = do
  let exts = SortedMap.fromList $ exts.asList <&> \namedSig => (fst $ internalise $ fst namedSig, namedSig)
  (x, weightingFuns, derived) <- evalStateT
                         (empty, empty)
                         [| (calc, deriveAll (empty @{TypeInfoEqByName}) []) |]
                         {stateType=(ListSet GenSignature, ListSet GenSignature)}
                         {m=Elab}
  let derived = sortBy (compare `on` declName . fst) $ derived ++ mapMaybe deriveWeightingFun (Prelude.toList weightingFuns)
  let (defs, bodies) = unzip derived
  pure (x, defs ++ bodies)
