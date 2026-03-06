||| A bridge between a single act of derivation (for a single type) and a user derivation task
module Deriving.DepTyCheck.Gen.ForAllNeededTypes.Impl

import public Control.Monad.State
import public Control.Monad.State.Tuple

import public Data.DPair
import public Data.List.Set
import public Data.SortedMap

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.ForOneType.Interface

%default total

--- Particular implementations producing the-core-derivation-function closure ---

ClosuringContext : (Type -> Type) -> Type
ClosuringContext m =
  ( MonadState  (ListSet GenSignature) m                                 -- gens already asked to be derived
  , MonadState  (List GenSignature, List GenSignature) m                 -- two queues of gens to be derived, one for known types, one the unknown ones
  , MonadState  (ListSet TypeInfo) m                                     -- type names that were asked for deriving their weighting function
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

deriveAll : NamesInfoInTypes => ConsRecs => DeriveBodyForType => DerivationClosure m => ClosuringContext m => Elaboration m =>
            List (Decl, Decl) -> m $ List (Decl, Decl)
deriveAll acc = do
  (toDeriveKnown, toDeriveUnknown) <- get {stateType=(List _, List _)}
  put ([], toDeriveUnknown)
  derived <- (++ acc) <$> for toDeriveKnown deriveOne
  if not $ null toDeriveKnown
    then assert_total deriveAll derived
    else if null toDeriveUnknown
      then pure derived
      else do
        (niit, cr) <- updateNamesAndConsRecs $ targetType <$> toDeriveUnknown
        put (toDeriveUnknown, [])
        assert_total $ deriveAll @{niit} @{cr} derived
  where
    deriveOne : GenSignature -> m (Decl, Decl)
    deriveOne sig = do
      let name = nameForGen sig
      -- derive declaration and body for the asked signature. It's important to call it AFTER update of the map in the state to not to cycle
      let genFunClaim = export' name $ canonicSig sig
      (tyWithWeightFuns, genFunBody) <- logBounds Info "deptycheck.derive.type" [sig] $ canonicBody sig name
      modify $ \old => foldl List.Set.insert' old tyWithWeightFuns
      pure (genFunClaim, def name genFunBody)

DeriveBodyForType => ClosuringContext m => Elaboration m => SortedMap GenSignature (ExternalGenSignature, Name) => DerivationClosure m where

  callGen sig fuel values = do

    -- look for external gens, and call it if exists
    let Nothing = lookupLengthChecked sig %search
      | Just (name, Element extSig lenEq) =>
          logValue Details "deptycheck.derive.closuring.external" [sig] "is used as an external generator" $
            (callExternalGen extSig name (var outmostFuelArg) $ rewrite lenEq in values, Just (_ ** extSig.gendOrder))

    -- put to derivation queue if necessary
    when (not !(gets $ contains sig)) $ do

      -- remember that we're responsible for this signature derivation
      modify $ insert sig

      -- remember the task to derive
      modify {stateType=(List _, List _)} $ if isTypeKnown sig.targetType then mapFst $ (::) sig else mapSnd $ (::) sig

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
  ((_, _, weightingFuns), (x, derived)) <- runStateT
                         (empty, (empty, empty), empty @{TypeInfoEqByName})
                         [| (calc, deriveAll []) |]
                         {stateType=(ListSet GenSignature, (List GenSignature, List GenSignature), ListSet TypeInfo)}
                         {m=Elab}
  let derived = sortBy (compare `on` declName . fst) $ derived ++ mapMaybe deriveWeightingFun (Prelude.toList weightingFuns)
  let (defs, bodies) = unzip derived
  pure (x, defs ++ bodies)
