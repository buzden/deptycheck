module Deriving.DepTyCheck.Gen.ConsRecs

import public Data.Alternative
import public Data.Fuel
import public Data.List.Ex
import public Data.Nat1
import public Data.SortedMap
import public Data.SortedMap.Extra
import public Data.SortedSet
import public Data.SortedSet.Extra

import public Deriving.DepTyCheck.Gen.Signature
import public Deriving.DepTyCheck.Gen.Tuning

import public Language.Reflection.Compat.TypeInfo
import public Language.Reflection.Logging

import public Syntax.IHateParens.Function

%default total

----------------------------------
--- Constructors recursiveness ---
----------------------------------

||| Weight info of recursive constructors
public export
data RecWeightInfo : Type where
  SpendingFuel : ((leftFuelVarName : Name) -> TTImp) -> RecWeightInfo
  StructurallyDecreasing : (decrTy : TypeInfo) -> (wExpr : TTImp) -> RecWeightInfo

public export
record ConWeightInfo where
  constructor MkConWeightInfo
  ||| Either a constant (for non-recursive) or a function returning weight info (for recursive)
  weight : Either Nat1 RecWeightInfo

liftWeight1 : TTImp
liftWeight1 = `(Data.Nat1.one)

export
reflectNat1 : Nat1 -> TTImp
reflectNat1 $ FromNat 1 = liftWeight1
reflectNat1 $ FromNat n = `(fromInteger ~(primVal $ BI $ cast n))

export
isWeight1 : TTImp -> Bool
isWeight1 = (== liftWeight1)

public export
weightExpr : ConWeightInfo -> Either TTImp ((leftFuelVarName : Name) -> TTImp)
weightExpr $ MkConWeightInfo $ Left n = Left $ reflectNat1 n
weightExpr $ MkConWeightInfo $ Right $ StructurallyDecreasing {wExpr, _} = Left wExpr
weightExpr $ MkConWeightInfo $ Right $ SpendingFuel e = Right e

export
usedWeightFun : ConWeightInfo -> Maybe TypeInfo
usedWeightFun $ MkConWeightInfo $ Right $ StructurallyDecreasing {decrTy, _} = Just decrTy
usedWeightFun $ MkConWeightInfo $ Right $ SpendingFuel _ = Nothing
usedWeightFun $ MkConWeightInfo $ Left _ = Nothing

export
record ConsRecs where
  constructor MkConsRecs
  ||| Map from a type name to a list of its constructors with their weight info
  conWeights : SortedMap Name $ (givenTyArgs : SortedSet Nat) -> List (Con, ConWeightInfo)
  ||| Derive a function for weighting type, if given type is weightable and needs a special function
  deriveWeightingFun : TypeInfo -> Maybe (Decl, Decl)

-- This is a workaround of some bad and not yet understood behaviour, leading to both compile- and runtime errors
removeNamedApps, workaroundFromNat : TTImp -> TTImp
removeNamedApps = mapTTImp $ \case INamedApp _ lhs _ _ => lhs; e => e
workaroundFromNat = mapTTImp $ \e => case fst $ unAppAny e of IVar _ `{Data.Nat1.FromNat} => removeNamedApps e; _ => e

weightFunName : TypeInfo -> Name
weightFunName ty = fromString "weight^\{show ty.name}"

-- this is a workarond for Idris compiler bug #2983
export
interimNamesWrapper : Name -> Name
interimNamesWrapper n = UN $ Basic "inter^<\{show n}>"

-- This function is moved out from `getConsRecs` to reduce the closure of the returned function
deriveW : SortedMap Name (Maybe a, List (con : Con ** Either Nat1 (b, SortedSet $ Fin con.args.length))) -> TypeInfo -> Maybe (Decl, Decl)
deriveW consRecs ty = do
  (decrArg, cons) <- lookup ty.tyName consRecs
  guard $ isJust decrArg -- continue only when this type has structurally decreasing argument
  let weightFunName = weightFunName ty

  let inTyArg = arg $ foldl (\f, n => namedApp f n $ var n) .| var ty.name .| mapMaybe name ty.args
  let funSig = export' weightFunName $ piAll `(Data.Nat1.Nat1) $ map {piInfo := ImplicitArg} ty.args ++ [inTyArg]

  let wClauses = cons <&> \(con ** e) => do
    let wArgs = either (const empty) snd e
    let lhsArgs : List (_, _) = mapI con.args $ \idx, arg => appArg arg <$> if contains idx wArgs && arg.count == MW
                                  then let bindName = UN $ Basic "arg^\{show idx}" in (Just bindName, bindVar bindName)
                                  else (Nothing, implicitTrue)
    let callSelfOn : Name -> TTImp
        callSelfOn n = var weightFunName .$ var n
    patClause (var weightFunName .$ (reAppAny .| var con.name .| snd <$> lhsArgs)) $ case mapMaybe fst lhsArgs of
      []  => liftWeight1
      [x] => `(succ ~(callSelfOn x))
      xs  => `(succ $ Prelude.concat @{Maximum} ~(liftList' $ xs <&> callSelfOn))

  pure (funSig, def weightFunName wClauses)

getAppVar : TTImp -> Maybe Name
getAppVar e = case fst $ unAppAny e of IVar _ n => Just n; _ => Nothing

-- TODO to think of better placement for this function; this anyway is intended to be called from the derived code.
public export
leftDepth : Fuel -> Nat1
leftDepth = go 1 where
  go : Nat1 -> Fuel -> Nat1
  go n Dry      = n
  go n (More x) = go (succ n) x

-- This function is moved out from `getConsRecs` to reduce the closure of the returned function
finCR : NamesInfoInTypes =>
        (tyName : Name) ->
        (wTyArgs : SortedMap Nat (TypeInfo, Name)) ->
        List (con : Con ** Either Nat1 (TTImp -> TTImp, SortedSet $ Fin con.args.length)) ->
        (givenTyArgs : SortedSet Nat) -> List (Con, ConWeightInfo)
finCR tyName wTyArgs cons givenTyArgs = do
  let wTyArgs = wTyArgs `intersectionMap` givenTyArgs
  cons <&> \(con ** e) => (con,) $ MkConWeightInfo $ e <&> \(wMod, directRecConArgs) => do
    let conRetTyArgs = snd $ unAppAny con.type
    let directRecConArgArgs = flip mapMaybe con.args $ \conArg => case unAppAny conArg.type of (conArgTy, conArgArgs) => do
                                toMaybe (getAppVar conArgTy == Just tyName) conArgArgs
    -- default behaviour, spend fuel, weight proportional to fuel
    fromMaybe (SpendingFuel $ wMod . app `(Deriving.DepTyCheck.Gen.ConsRecs.leftDepth) . var) $ do
    -- work only with given args
    -- fail-fast if no given weightable args
    guard $ not $ null wTyArgs
    -- If for any weightable type argument (in `wTyArgs`) there exists a directly recursive constructor arg (in `directRecConArgs`) that has
    -- this type argument strictly decreasing, we consider this constructor to be non-fuel-spending.
    let conArgNames = SortedSet.fromList $ mapMaybe name con.args
    (decrTy, weightExpr) <- foldAlt' wTyArgs.asList $ \(wTyArg, weightTy, weightArgName) => map (weightTy,) $ do
      conRetTyArg <- getExpr <$> getAt wTyArg conRetTyArgs
      guard $ isJust $ lookupCon =<< getAppVar conRetTyArg
      let freeNamesLessThanOrig = allVarNames' conRetTyArg `intersection` conArgNames
      foldAlt' directRecConArgArgs $ \conArgArgs => do
        getAt wTyArg conArgArgs >>= getAppVar . getExpr >>= \arg => toMaybe .| contains arg freeNamesLessThanOrig .|
          var (weightFunName weightTy) .$ var (interimNamesWrapper weightArgName)
    pure $ StructurallyDecreasing decrTy $ wMod weightExpr

export
getConsRecs : Elaboration m => NamesInfoInTypes => m ConsRecs
getConsRecs = do
  consRecs <- for knownTypes $ \targetType => logBounds {level=DetailedTrace} "deptycheck.derive.consRec" [targetType] $ do
    crsForTy <- for targetType.cons $ \con => do
      tuneImpl <- search $ ProbabilityTuning con.name
      w : Either Nat1 (TTImp -> TTImp, SortedSet $ Fin con.args.length) <- case isRecursive {containingType=Just targetType} con of
        --             ^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^ <- set of directly recursive constructor arguments
        --                    \------ Modifier of the standard weight expression
        False => pure $ Left $ maybe one (\impl => tuneWeight @{impl} one) tuneImpl
        True  => Right <$> do
          fuelWeightExpr <- case tuneImpl of
            Nothing   => pure id
            Just impl => quote (tuneWeight @{impl}) <&> \wm, expr => workaroundFromNat $ wm `applySyn` expr
          let directlyRecArgs : List $ Fin con.args.length := flip mapMaybe con.args.withIdx $ \idxarg => do
            argTy <- getAppVar (snd idxarg).type
            whenT .| argTy == targetType.name .| fst idxarg
          when (not $ null directlyRecArgs) $
            logPoint {level=FineDetails} "deptycheck.derive.consRec" [targetType, con]
              "- directly recursive args: \{show $ finToNat <$> directlyRecArgs}"
          pure (fuelWeightExpr, fromList directlyRecArgs)
      pure (con ** w)
    -- determine if this type is a nat-or-list-like data, i.e. one which we can measure for the probability
    let weightable = flip any crsForTy $ \case (_ ** Right (_, dra)) => not $ null dra; _ => False
    pure (toMaybe weightable targetType, crsForTy)
  let 0 _ : SortedMap Name (Maybe TypeInfo, List (con : Con ** Either Nat1 (TTImp -> TTImp, SortedSet $ Fin con.args.length))) := consRecs

  let weightableTyArgs : (ars : List Arg) -> SortedMap Nat (TypeInfo, Name) -- <- a map from Fin ars.length to a weightable type and its argument name
      weightableTyArgs ars = fromList $ flip List.mapMaybe ars.withIdx $ \(idx, ar) =>
                               getAppVar ar.type >>= lookup' consRecs <&> fst >>= \tyN => [| (finToNat idx,,) tyN ar.name |]
  let finalConsRecs = mapWithKey' consRecs $ \tyName, (_, cons) => do
    finCR tyName (maybe SortedMap.empty .| weightableTyArgs . args .| lookupType tyName) cons

  pure $ MkConsRecs finalConsRecs $ deriveW consRecs

export
lookupConsWithWeight : ConsRecs => GenSignature -> Maybe $ List (Con, ConWeightInfo)
lookupConsWithWeight @{crs} sig = do
  let givs = mapIn finToNat sig.givenParams
  lookup' crs.conWeights sig.targetType.name <&> (`apply` givs)

export
deriveWeightingFun : ConsRecs => TypeInfo -> Maybe (Decl, Decl)
deriveWeightingFun @{crs} n = crs.deriveWeightingFun n
