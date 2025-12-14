module Deriving.DepTyCheck.Gen.ConsRecs

import public Data.Alternative
import public Data.Fuel
import public Data.List.Ex
import public Data.List.Map
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

record ConRec where
  constructor MkConRec
  constr    : Con
  conWeight : Either Nat1 (TTImp -> TTImp, SortedSet $ Fin constr.args.length)
           -- ^^^^^^                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
           --    |                                   \- directly recursive args
           --    \- `Left` for non-recursive, `Right` for recursive constructor

-- determine if this type is a nat-or-list-like data, i.e. one which we can measure for the probability
weightableTy : List ConRec -> Bool
weightableTy = any weightableCon where
  weightableCon : ConRec -> Bool
  weightableCon $ MkConRec _ $ Right (_, dra) = not $ null dra
  weightableCon $ MkConRec _ $ Left _         = False

record TyConsRec where
  constructor MkTyConsRec
  typeInfo         : TypeInfo
  weightableItself : Bool -- well, this piece is redundant, since it always equals to `weightableTy constructors`
  weightableTyArgs : SortedMap (Fin typeInfo.args.length) (TypeInfo, Name)
  constructors     : List ConRec

export
record ConsRecs where
  constructor MkConsRecs
  consRecs : SortedMap Name TyConsRec

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
deriveW : TyConsRec -> Maybe (Decl, Decl)
deriveW $ MkTyConsRec ty weightable _ cons = do
  guard weightable -- continue only when this type has structurally decreasing argument
  let weightFunName = weightFunName ty

  let inTyArg = arg $ foldl (\f, n => namedApp f n $ var n) .| var ty.name .| mapMaybe name ty.args
  let funSig = export' weightFunName $ piAll `(Data.Nat1.Nat1) $ map {piInfo := ImplicitArg} ty.args ++ [inTyArg]

  let wClauses = cons <&> \(MkConRec con e) => do
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
        (tyCR : TyConsRec) ->
        (givenTyArgs : SortedSet $ Fin tyCR.typeInfo.args.length) ->
        List (Con, ConWeightInfo)
finCR (MkTyConsRec ti _ wTyArgs cons) givenTyArgs = do
  let wTyArgs = wTyArgs `intersectionMap` givenTyArgs
  cons <&> \(MkConRec con e) => (con,) $ MkConWeightInfo $ e <&> \(wMod, directRecConArgs) => do
    let conRetTyArgs = snd $ unAppAny con.type
    let directRecConArgArgs = flip mapMaybe con.args $ \conArg => case unAppAny conArg.type of (conArgTy, conArgArgs) => do
                                toMaybe (getAppVar conArgTy == Just ti.name) conArgArgs
    -- default behaviour, spend fuel, weight proportional to fuel
    fromMaybe (SpendingFuel $ wMod . app `(Deriving.DepTyCheck.Gen.ConsRecs.leftDepth) . var) $ do
    -- work only with given args
    -- fail-fast if no given weightable args
    guard $ not $ null wTyArgs
    -- If for any weightable type argument (in `wTyArgs`) there exists a directly recursive constructor arg (in `directRecConArgs`) that has
    -- this type argument strictly decreasing, we consider this constructor to be non-fuel-spending.
    let conArgNames = SortedSet.fromList $ mapMaybe name con.args
    (decrTy, weightExpr) <- foldAlt' wTyArgs.asList $ \(wTyArg, weightTy, weightArgName) => map (weightTy,) $ do
      let wTyArg = finToNat wTyArg
      conRetTyArg <- getExpr <$> getAt wTyArg conRetTyArgs
      guard $ isJust $ lookupCon =<< getAppVar conRetTyArg
      let freeNamesLessThanOrig = allVarNames' conRetTyArg `intersection` conArgNames
      foldAlt' directRecConArgArgs $ \conArgArgs => do
        getAt wTyArg conArgArgs >>= getAppVar . getExpr >>= \arg => toMaybe .| contains arg freeNamesLessThanOrig .|
          var (weightFunName weightTy) .$ var (interimNamesWrapper weightArgName)
    pure $ StructurallyDecreasing decrTy $ wMod weightExpr

weightableTyArgs : (consRecs : SortedMap Name (TypeInfo, Bool, List ConRec)) -> (ti : TypeInfo) -> SortedMap (Fin ti.args.length) (TypeInfo, Name)
weightableTyArgs consRecs ti = fromList $ flip List.mapMaybe ti.args.withIdx $ \(idx, ar) =>
  getAppVar ar.type >>= lookup' consRecs >>= \(wti, weightable, _) => guard weightable >> (idx, wti,) <$> ar.name

export
getConsRecs : Elaboration m => NamesInfoInTypes => m ConsRecs
getConsRecs = do
  consRecs <- for (toSortedMap knownTypes) $ \targetType => logBounds DetailedTrace "deptycheck.derive.consRec" [targetType] $ do
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
            logPoint FineDetails "deptycheck.derive.consRec" [targetType, con]
              "- directly recursive args: \{show $ finToNat <$> directlyRecArgs}"
          pure (fuelWeightExpr, fromList directlyRecArgs)
      pure $ MkConRec con w
    pure (targetType, weightableTy crsForTy, crsForTy)
  let 0 _ : SortedMap Name (TypeInfo, Bool, List ConRec) := consRecs

  pure $ MkConsRecs $ mapWithKey' consRecs $ \tyName, (ti, wbl, cons) => do
    MkTyConsRec ti wbl (weightableTyArgs consRecs ti) cons

export
lookupConsWithWeight : ConsRecs => NamesInfoInTypes => GenSignature -> Maybe $ List (Con, ConWeightInfo)
lookupConsWithWeight @{MkConsRecs crs} sig = do
  cr <- lookup sig.targetType.name crs
  let Yes prf = decEq cr.typeInfo.args.length sig.targetType.args.length | No _ => Nothing
  pure $ finCR cr $ rewrite prf in sig.givenParams

export
deriveWeightingFun : ConsRecs => TypeInfo -> Maybe (Decl, Decl)
deriveWeightingFun @{MkConsRecs crs} ti = lookup ti.name crs >>= deriveW
