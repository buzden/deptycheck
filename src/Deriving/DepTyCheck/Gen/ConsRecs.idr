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
  ||| Along with the weight, contains a weight expression for the case when the constructor needs to spend fuel after all
  StructurallyDecreasing : (decrTy : TypeInfo) -> (wExpr : TTImp) -> (spendingFuelWExpr : (leftFuelVarName : Name) -> TTImp) -> RecWeightInfo

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
  weightableTyArgs : SortedMap (Fin typeInfo.args.length) (TypeInfo, Name)
  constructors     : List ConRec

export
record ConsRecs where
  constructor MkConsRecs
  consRecs : SortedMap Name TyConsRec

Semigroup ConsRecs where
  MkConsRecs cw <+> MkConsRecs cw' = MkConsRecs $ cw `mergeLeft` cw'

-------------------------------------
--- Getting (deriving) `ConsRecs` ---
-------------------------------------

-- This is a workaround of some bad and not yet understood behaviour, leading to both compile- and runtime errors
removeNamedApps, workaroundFromNat : TTImp -> TTImp
removeNamedApps = mapTTImp $ \case INamedApp _ lhs _ _ => lhs; e => e
workaroundFromNat = mapTTImp $ \e => case fst $ unAppAny e of IVar _ `{Data.Nat1.FromNat} => removeNamedApps e; _ => e

weightFunName : TypeInfo -> Name
weightFunName ty = fromString "weight^\{show ty.name}"

-- this is a workaround for Idris compiler bug #2983
export
interimNamesWrapper : Name -> Name
interimNamesWrapper n = UN $ Basic "inter^<\{show n}>"

-- This function is moved out from `getConsRecs` to reduce the closure of the returned function
deriveW : TyConsRec -> Maybe (Decl, Decl)
deriveW $ MkTyConsRec ty _ cons = do
  guard $ weightableTy cons -- continue only when this type has structurally decreasing argument
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
finCR (MkTyConsRec ti wTyArgs cons) givenTyArgs = do
  let wTyArgs = wTyArgs `intersectionMap` givenTyArgs
  cons <&> \(MkConRec con e) => (con,) $ MkConWeightInfo $ e <&> \(wMod, directRecConArgs) => do
    let conRetTyArgs = snd $ unAppAny con.type
    let directRecConArgArgs = flip mapMaybe con.args $ \conArg => case unAppAny conArg.type of (conArgTy, conArgArgs) => do
                                toMaybe (getAppVar conArgTy == Just ti.name) conArgArgs
    -- default behaviour, spend fuel, weight proportional to fuel
    let spendingFuelWExpr = wMod . app `(Deriving.DepTyCheck.Gen.ConsRecs.leftDepth) . var
    fromMaybe (SpendingFuel spendingFuelWExpr) $ do
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
    pure $ StructurallyDecreasing decrTy (wMod weightExpr) spendingFuelWExpr

weightableTyArgs : (consRecs : SortedMap Name (TypeInfo, List ConRec)) -> (ti : TypeInfo) -> SortedMap (Fin ti.args.length) (TypeInfo, Name)
weightableTyArgs consRecs ti = fromList $ flip List.mapMaybe ti.args.withIdx $ \(idx, ar) =>
  getAppVar ar.type >>= lookup' consRecs >>= \(wti, cons) => guard (weightableTy cons) >> (idx, wti,) <$> ar.name

-- Builds `ConsRecs` only for the given types, assuming that given `NamesInfoInTypes` contains info for them and their dependencies
getConsRecsFor : NamesInfoInTypes => Elaboration m => (desiredTypes : ListMap Name TypeInfo) -> m ConsRecs
getConsRecsFor desiredTypes = do
  consRecs <- for (toSortedMap desiredTypes) $ \targetType => logBounds DetailedTrace "deptycheck.derive.consRec" [targetType] $ do
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
    pure (targetType, crsForTy)
  let 0 _ : SortedMap Name (TypeInfo, List ConRec) := consRecs

  pure $ MkConsRecs $ mapWithKey' consRecs $ \tyName, (ti, cons) => do
    MkTyConsRec ti (weightableTyArgs consRecs ti) cons

export
getConsRecs : NamesInfoInTypes => Elaboration m => m ConsRecs
getConsRecs = getConsRecsFor knownTypes

export
lookupConsWithWeight : ConsRecs => NamesInfoInTypes => GenSignature -> Maybe $ List (Con, ConWeightInfo)
lookupConsWithWeight @{MkConsRecs crs} sig = do
  cr <- lookup sig.targetType.name crs
  let Yes prf = decEq cr.typeInfo.args.length sig.targetType.args.length | No _ => Nothing
  pure $ finCR cr $ rewrite prf in sig.givenParams

export
deriveWeightingFun : ConsRecs => TypeInfo -> Maybe (Decl, Decl)
deriveWeightingFun @{MkConsRecs crs} ti = lookup ti.name crs >>= deriveW

export
isTypeKnown : ConsRecs => TypeInfo -> Bool
isTypeKnown @{MkConsRecs crs} ti = isJust $ lookup ti.name crs

-- Having a `ConsRecs` being built from the given `NamesInfoInTypes`,
-- it'll get the updated `NamesInfoInTypes` and a `ConsRecs` equivalent to those being built from this `NamesInfoInTypes`, but more effective.
export
updateNamesAndConsRecs : NamesInfoInTypes => ConsRecs => Elaboration m => List TypeInfo -> m (NamesInfoInTypes, ConsRecs)
updateNamesAndConsRecs @{niit} @{crs} tis = do
  newNiit <- logBounds Trace "deptycheck.derive.namesInfo.update" [] $ enrichNamesInfoInTypes tis niit
  newCr <- logBounds Trace "deptycheck.derive.consRec.update" [] $ map (crs <+>) $ getConsRecsFor @{newNiit} $ fromList $ tis <&> \ti => (ti.name, ti)
  pure (newNiit, newCr)

-----------------------------------------------------
--- Termination of non-fuel-spending constructors ---
-----------------------------------------------------

-- Size changes of arguments in a call of a function done by this function itself, see `selfCallSizeChanges` below
SelfCall : Type
SelfCall = List $ List $ Maybe Bool

-- Tells how the second expression relates to the first one structurally, in the way the totality checker does it:
-- `Just True` is for being smaller, `Just False` is for being the same, `Nothing` is for unknown.
-- Arguments of the same data constructor are compared only up to the given depth, like the totality checker does.
sizeChange : NamesInfoInTypes => (depth : Nat) -> (from, to : TTImp) -> Maybe Bool
sizeChange depth from to = do
  let (fromFun, fromArgs) = mapSnd (map getExpr) $ unAppAny from
  let (toFun, toArgs) = mapSnd (map getExpr) $ unAppAny to
  -- an expression is the same as itself and as its application to more arguments, since the totality checker compares
  -- an application by its function; arguments are compared by their positions, which is enough for normalised types of constructors
  if toFun == fromFun && length fromArgs <= length toArgs && all (uncurry (==)) (fromArgs `zip` toArgs) then Just False else do
  -- only data constructors are looked into, since matching on a type constructor does not make its arguments smaller
  let IVar _ con = fromFun
    | _ => Nothing
  guard $ isJust (lookupCon con) && isNothing (lookupType con)
  -- an expression which is not bigger than an argument of a data constructor is smaller than the whole application
  -- (this and the next recursive calls are total since they are done for arguments of the given application)
  if any (\fromArg => isJust $ assert_total $ sizeChange (pred depth) fromArg to) fromArgs then Just True else do
  -- an application of the same data constructor is smaller when none of its arguments is of unknown size and some of them is smaller
  let S depth = depth
    | Z => Nothing
  guard $ toFun == fromFun && length toArgs == length fromArgs
  changes <- for (fromArgs `zip` toArgs) $ \(fromArg, toArg) => assert_total $ sizeChange depth fromArg toArg
  toMaybe (any id changes) True

-- Tells how arguments change in a call of a function done by this function itself.
-- For each argument of the caller (the outer list) and for each argument of the callee (the inner lists),
-- `Just True` is for the callee's one being structurally smaller, `Just False` is for being the same, `Nothing` is for unknown.
-- Arguments of the callee which are `Nothing` are those that cannot be related to arguments of the caller.
selfCallSizeChanges : NamesInfoInTypes => (callerArgs : List TTImp) -> (calleeArgs : List $ Maybe TTImp) -> SelfCall
selfCallSizeChanges callerArgs calleeArgs = callerArgs <&> \callerArg => calleeArgs <&> (>>= sizeChange totalityDepth callerArg) where
  -- the default value of `%totality_depth` of the compiler is assumed, since the actual value is not available
  totalityDepth : Nat
  totalityDepth = 5

-- NOTE: Monadic binds of pure values are used below in order not to evaluate these values each time they are used.

-- Drops all rows that decrease in a lexicographic order of columns, the order is the same for all dropped rows; returns rows that are left.
-- A column is the next one in the order when no left row is unknown in it; then all rows that are smaller in this column are dropped.
-- At least one row is dropped on each step, so the count of rows is enough steps; this argument makes the function total.
dropDecreasing : Monad m => (steps : Nat) -> List (a, List $ Maybe Bool) -> m $ List (a, List $ Maybe Bool)
dropDecreasing Z         rows = pure rows
dropDecreasing (S steps) rows = do
  let col : Nat -> List $ Maybe Bool
      col idx = rows <&> join . getAt idx . snd
  let cols = finToNat <$> List.allFins (maybe 0 (length . snd) $ head' rows)
  Just idx <- pure $ List.find (\idx => all isJust (col idx) && any (== Just True) (col idx)) cols
    | Nothing => pure rows
  rows <- pure $ filter ((/= Just True) . join . getAt idx . snd) rows
  dropDecreasing steps rows

-- Checks the size-change termination principle for a function calling itself with given changes of its arguments:
-- each idempotent composition of the calls must have an argument which is strictly decreasing.
-- When there are too many different compositions, the answer is negative, to be on the safe side.
sizeChangeTerminating : Monad m => (calls : List SelfCall) -> m Bool
sizeChangeTerminating calls = go maxCompositions [] calls where
  maxCompositions : Nat
  maxCompositions = 32
  compose : (first, second : SelfCall) -> SelfCall
  compose first second = first <&> \fromCaller => transpose second <&> \toCallee =>
                           foldl max Nothing $ zipWith (\x, y => (\a, b => a || b) <$> x <*> y) fromCaller toCallee
  nonDecreasing : SelfCall -> Bool
  nonDecreasing call = all (\(idx, changes) => getAt (finToNat idx) changes /= Just (Just True)) call.withIdx
  -- each round gives at least one new composition, so the count of rounds is limited by the limit of compositions too
  go : (rounds : Nat) -> (old, new : List SelfCall) -> m Bool
  go _          _   []  = pure True
  go Z          _   _   = pure False
  go (S rounds) old new = do
    False <- pure $ any (\call => nonDecreasing call && compose call call == call) new || length old + length new > maxCompositions
      | True => pure False
    old <- pure $ old ++ new
    new <- pure $ filter (not . flip elem old) $ nub [| compose new calls |]
    go rounds old new

||| Tells which of given non-fuel-spending constructors need to spend fuel, since otherwise calls of the generator done by them
||| can be non-terminating. Each constructor goes with all calls of the same generator done by it; each call is a pair
||| of expressions of given type arguments in the constructor's result type and of ones in the call;
||| a `Nothing` among the latter is for an argument which the totality checker cannot relate to arguments of the caller.
export
needFuelToTerminate : NamesInfoInTypes => Monad m => List (Name, List (List TTImp, List $ Maybe TTImp)) -> m $ List Name
needFuelToTerminate consCalls = do
  cons <- pure $ consCalls <&> mapSnd (map $ uncurry selfCallSizeChanges)
  -- calls decreasing in a single lexicographic order of given type arguments are terminating, only changes of the same arguments matter here
  rows <- pure $ nub $ cons >>= \(con, selfCalls) => selfCalls <&> \selfCall =>
            (con, selfCall.withIdx <&> \(idx, changes) => join $ getAt (finToNat idx) changes)
  notOrdered <- pure $ nub $ fst <$> !(dropDecreasing (length rows) rows)
  let False = null notOrdered
    | True => pure []
  -- calls of the rest constructors still can be terminating due to changes between different arguments;
  -- they must terminate both for each constructor separately and for all non-fuel-spending constructors together
  let callsOf : (Name -> Bool) -> List SelfCall
      callsOf p = nub $ cons >>= \(con, selfCalls) => if p con then selfCalls else []
  nonTerminating <- map (map fst . filter (not . snd)) $ for notOrdered $ \con => (con,) <$> sizeChangeTerminating !(pure $ callsOf (== con))
  allTerminating <- sizeChangeTerminating !(pure $ callsOf $ not . flip elem nonTerminating)
  pure $ if allTerminating then nonTerminating else notOrdered

||| Makes a non-fuel-spending constructor to be a fuel-spending one
export
asFuelSpending : ConWeightInfo -> ConWeightInfo
asFuelSpending $ MkConWeightInfo $ Right $ StructurallyDecreasing {spendingFuelWExpr, _} = MkConWeightInfo $ Right $ SpendingFuel spendingFuelWExpr
asFuelSpending w = w
