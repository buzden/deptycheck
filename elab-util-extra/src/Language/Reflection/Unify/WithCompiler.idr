module Language.Reflection.Unify.WithCompiler

import Control.Monad.Either
import Control.Monad.Writer
import Control.Monad.Identity
import Data.DPair
import Data.Fin.Set
import Data.Vect
import Data.Vect.Quantifiers
import Data.SnocVect
import Data.SortedMap
import Decidable.Equality
import Language.Reflection
import Language.Reflection.Expr
import Language.Reflection.Logging
import Language.Reflection.Syntax
import Language.Reflection.Unify.Interface
import Language.Reflection.VarSubst

%default total

||| Generate free variable name to index mapping
genNameToId :
  {freeVars : Nat} ->
  Vect freeVars FVData ->
  SortedMap Name $ Fin freeVars
genNameToId fvs =
  foldl (\acc, (i, fv) => insert fv.name i acc) empty (zip (allFins freeVars) fvs)

||| Generate free variable hole to index mapping
genHoleToId :
  {freeVars : Nat} ->
  Vect freeVars FVData ->
  SortedMap String $ Fin freeVars
genHoleToId fvs =
  foldl (\acc, (i, fv) => insert fv.holeName i acc) empty (zip (allFins freeVars) fvs)

aMHImpl :
  {0 freeVars : Nat} ->
  MonadWriter (FinSet freeVars) m =>
  SortedMap String (Fin freeVars) ->
  TTImp ->
  m TTImp
aMHImpl h2Id h = do
  let IHole _ s = h
  | _ => pure h
  let Just id = lookup s h2Id
  | _ => pure h
  writer (h, insert id empty)

||| Generate a set of free variables whose holes appear in a TTImp
allMatchingHoles :
  {0 freeVars : Nat} ->
  SortedMap String (Fin freeVars) ->
  TTImp ->
  FinSet freeVars
allMatchingHoles h2Id t = execWriter $ mapMTTImp (aMHImpl h2Id) t

fromPiInfo : Lazy t -> PiInfo t -> t
fromPiInfo _ (DefImplicit x) = x
fromPiInfo x _ = x

||| Generate a dependency map from unification output and hole-to-index mapping
genDeps :
  {freeVars : Nat} ->
  Vect freeVars FVData ->
  SortedMap String (Fin freeVars) ->
  Vect freeVars $ FVDeps freeVars
genDeps fvs h2Id =
  map
    (\fv =>
      MkFVDeps
        (allMatchingHoles h2Id fv.type)
        (fromMaybe empty $ allMatchingHoles h2Id <$> fv.value)
        (fromPiInfo empty $ allMatchingHoles h2Id <$> fv.piInfo)
    )
    fvs

||| Find free variables without value
genEmpties :
  {freeVars : Nat} ->
  Vect freeVars FVData ->
  FinSet freeVars
genEmpties fvs = foldl genEmpties' empty $ zip (allFins freeVars) fvs
  where
    genEmpties' : FinSet fv -> (Fin fv, FVData) -> FinSet fv
    genEmpties' set (i, fv) =
      if isNothing fv.value
         then insert i set
         else set

||| Generate a dependency graph based on free variable data
genDG :
  {freeVars : Nat} ->
  Vect freeVars FVData ->
  DependencyGraph
genDG fvs = do
  let h2Id = genHoleToId fvs
  MkDG freeVars fvs (genDeps fvs h2Id) (genEmpties fvs) (genNameToId fvs) h2Id

||| Find all free variables that can be substituted
canSub :
  (dg : DependencyGraph) ->
  FinSet dg.freeVars
canSub dg =
  flip difference dg.empties $
    foldl
      (\s, (i, deps) =>
        if (flip difference dg.empties (mergeDeps deps)) == empty
           then insert i s
           else s)
      Fin.Set.empty
      $ zip (allFins dg.freeVars) dg.fvDeps

subMatchingHolesImpl :
  (dg : DependencyGraph) ->
  FinSet dg.freeVars ->
  TTImp ->
  TTImp
subMatchingHolesImpl dg fbs ih@(IHole _ h) =
  case lookup h dg.holeToId of
    Just id =>
      if contains id fbs
        then
          let fv = index id dg.fvData
          in fromMaybe ih fv.value
        else ih
    Nothing => ih
subMatchingHolesImpl _ _ t = t

||| Substitute all holes matching free variables in set with their values
subMatchingHoles :
  (dg : DependencyGraph) ->
  FinSet dg.freeVars ->
  TTImp ->
  TTImp
subMatchingHoles dg fbs = mapTTImp $ subMatchingHolesImpl dg fbs

||| Substitute all free variables in set within other free variable's data
fvSubMatching :
  (dg: DependencyGraph) ->
  FinSet dg.freeVars ->
  FVData ->
  FVData
fvSubMatching dg canSub =
  { type $= subMatchingHoles dg canSub
  , value $= map $ subMatchingHoles dg canSub
  , piInfo $= map $ subMatchingHoles dg canSub
  }

valDepsOfVar : (dg : DependencyGraph) -> Fin dg.freeVars -> FinSet dg.freeVars
valDepsOfVar dg id = valueDeps $ index id dg.fvDeps

valDepsOfVars : (dg : DependencyGraph) -> FinSet dg.freeVars -> FinSet dg.freeVars
valDepsOfVars dg vars = foldl (\a, b => union (valDepsOfVar dg b) a) empty (toList vars)

fvSubMatching' :
  (dg: DependencyGraph) ->
  FinSet dg.freeVars ->
  (FVData, FVDeps dg.freeVars) ->
  (FVData, FVDeps dg.freeVars)
fvSubMatching' dg canSub (fvData, MkFVDeps tyDeps valDeps piInfoDeps) = do
  let matchingHolesTy = allMatchingHoles dg.holeToId fvData.type
  let matchingHolesVal = fromMaybe empty $ allMatchingHoles dg.holeToId <$> fvData.value
  let matchingHolesPiInfo = fromPiInfo empty $ allMatchingHoles dg.holeToId <$> fvData.piInfo
  let canSubTy = intersection matchingHolesTy canSub
  let canSubVal = intersection matchingHolesVal canSub
  let canSubPiInfo = intersection matchingHolesPiInfo canSub
  let tyAddDeps = valDepsOfVars dg canSubTy
  let valAddDeps = valDepsOfVars dg canSubVal
  let piInfoAddDeps = valDepsOfVars dg canSubPiInfo
  let newTyDeps = union tyAddDeps (difference tyDeps canSubTy)
  let newValDeps = union valAddDeps (difference valDeps canSubVal)
  let newPiInfoDeps = union piInfoAddDeps (difference piInfoDeps canSubPiInfo)
  (fvSubMatching dg canSub fvData, MkFVDeps newTyDeps newValDeps newPiInfoDeps)


||| Substitute all free variables in set within dependency graph
doSub :
  (dg : DependencyGraph) ->
  FinSet dg.freeVars ->
  DependencyGraph
doSub dg canSub = do
  let (newFvData, newFvDeps) = unzip $ fvSubMatching' dg canSub <$> zip dg.fvData dg.fvDeps
  ({fvData := newFvData, fvDeps := newFvDeps} dg)

subEmptiesTImpl : (dg : DependencyGraph) -> TTImp -> TTImp
subEmptiesTImpl dg t@(IHole _ h) = do
  let Just id = lookup h dg.holeToId
  | _ => t
  if contains id dg.empties
    then
      let fv = index id dg.fvData
      in IVar EmptyFC fv.name
    else t
subEmptiesTImpl dg t = t

subEmptiesT : DependencyGraph -> TTImp -> TTImp
subEmptiesT dg = mapTTImp $ subEmptiesTImpl dg

subEmptiesFV :
  (dg: DependencyGraph) ->
  FVData ->
  FVData
subEmptiesFV dg  =
  { type $= subEmptiesT dg
  , value $= map $ subEmptiesT dg
  }

||| Substitute holes of empty free variables with their names
subEmpties :
  (dg : DependencyGraph) ->
  DependencyGraph
subEmpties dg = {fvData $= map $ subEmptiesFV dg} dg

||| Solve dependency graph
solveDG :
  (dg : DependencyGraph) ->
  DependencyGraph
solveDG dg = do
  let cs = canSub dg
  let False = null cs
  | _ => dg
  let ds = doSub dg cs
  -- DG <= DS because cs is non-empty, and every doSub may shrink the set of possibly substitutable variables
  -- If doSub can't shrink it, the dependency graph stays the same
  if ds == dg
     then dg
     else solveDG $ assert_smaller dg ds

ArgDPair : Type
ArgDPair = Subset Arg IsNamedArg

||| Generate hole name for free variables
genHoleNames :
  Elaboration m =>
  SnocVect l ArgDPair ->
  m $ (SortedMap Name String, SnocVect l String)
genHoleNames [<] = pure (empty, [<])
genHoleNames (xs :< (Element fv isNamed)) = do
  let n = argName fv
  gs <- genSym $ show n
  (others, others') <- genHoleNames xs
  pure $ (insert n (show gs) others, others' :< show gs)

||| Build up dependent pair type for typechecking
buildUpDPair : SnocVect l ArgDPair -> TTImp -> TTImp
buildUpDPair [<] t = t
buildUpDPair (xs :< (Element fv isNamed)) t =
  buildUpDPair xs
    `(Builtin.DPair.DPair
      ~(fv.type)
      ~(ILam EmptyFC MW ExplicitArg (Just $ argName fv) fv.type t))

||| Build up dependent pair value for typechecking
buildUpTarget : SnocVect l (String, ArgDPair) -> TTImp -> TTImp
buildUpTarget [<] t = t
buildUpTarget (xs :< (s, _)) t =
  buildUpTarget xs `((~(IHole EmptyFC s) ** ~t))

extractFVData :
  Elaboration m =>
  MonadError UnificationError m =>
  (t : Type) ->
  t ->
  Vect l ArgDPair ->
  Vect l String ->
  m $ Vect l (Name, TTImp, Maybe TTImp)
extractFVData t v ((Element fv isNamed) :: xs) (hn :: hns) = do
  case t of
    DPair myTy dNext => do
      let (vv ** vRest) = v
      quoteV <- quote vv
      quoteT <- quote myTy
      rest <- extractFVData (dNext vv) vRest xs hns
      let retVal =
        case quoteV of
            IHole _ hh =>
              if hh == hn then Nothing else Just quoteV
            qv => Just qv
      pure $ (argName fv, quoteT, retVal) :: rest
    _ => do
      qT <- quote t
      throwError $ ExtractionError $ qT
extractFVData t v [] [] = do
  qT <- quote t
  qV <- quote v
  case t of
    Equal x y =>
      case qV of
        INamedApp _ (INamedApp _ `(Builtin.Refl) _ _) _ _ => pure ()
        _ => throwError $ PostponeError
    _ => throwError $ InternalError "DPairs don't correspond to each other. Should never occur."
  pure []

||| Run unification
unify' :
  Elaboration m =>
  MonadError UnificationError m =>
  UnificationTask ->
  m $ DependencyGraph
unify' task = do
  let 0 allFVsNamed = task.lhsAreNamed ++ task.rhsAreNamed
  let allFreeVars = pushIn (task.lhsFreeVars ++ task.rhsFreeVars) allFVsNamed
  let snocLFV : SnocVect task.lfv _ =
    cast $ pushIn task.lhsFreeVars task.lhsAreNamed
  let snocRFV : SnocVect task.rfv _ =
    cast $ pushIn task.rhsFreeVars task.rhsAreNamed
  (lhsNMap, lhsNames) <- genHoleNames snocLFV
  (rhsNMap, rhsNames) <- genHoleNames snocRFV
  let hole2N = IHole EmptyFC <$> mergeLeft lhsNMap rhsNMap
  let allNames = lhsNames ++ rhsNames
  -- Assemble the type, the value of which is all our free variables + proof of equality
  let checkTargetType =
    buildUpDPair snocLFV $
      buildUpDPair snocRFV `(~(task.lhsExpr) ~=~ ~(task.rhsExpr))
  -- Assemble the value (holes + Refl)
  let checkTarget =
    buildUpTarget (zip lhsNames snocLFV) $
      buildUpTarget (zip rhsNames snocRFV) `(Refl)
  logPoint {level=DetailedTrace} "unifyWithCompiler" [] "Target type: \{show checkTargetType}"
  logPoint {level=DetailedTrace} "unifyWithCompiler" [] "Target value: \{show checkTarget}"
  -- Instantiate target type
  Just checkTargetType' : Maybe Type <-
    try (Just <$> check checkTargetType) (pure Nothing)
  | _ => throwError $ TargetTypeError checkTargetType
  -- Run unification
  Just checkTarget' : Maybe checkTargetType' <-
    try (Just <$> check checkTarget) (pure Nothing)
  | _ => throwError NoUnificationError
  ctQuote <- quote checkTarget'
  logPoint {level=DetailedTrace} "unifyWithCompiler" [] "Target value after quoting: \{show ctQuote}"
  let vectNames = cast allNames
  -- Extract unification results
  uniResults <-
    extractFVData checkTargetType' checkTarget' allFreeVars vectNames
  logPoint {level=DetailedTrace} "unifyWithCompiler" [] "Raw unification results: \{show uniResults}"
  -- Generate dependency graph
  let allZipped = zip vectNames $ zip (task.lhsFreeVars ++ task.rhsFreeVars) uniResults
  let dg = genDG $ makeFVData <$> allZipped
  let dg = {fvData $= map {piInfo $= map $ substituteVariables hole2N}} dg
  -- logPoint {level=DetailedTrace} "unifyWithCompiler" [] "InitialDG: \{show dg}"
  let dg = subEmpties dg
  -- logPoint {level=DetailedTrace} "unifyWithCompiler" [] "DG after subEmpties: \{show dg}"
  let solved = solveDG dg
  -- logPoint {level=DetailedTrace} "unifyWithCompiler" [] "Solved DG: \{show solved}"
  pure solved

||| Run unification in a try block
export
unifyWithCompiler :
  Elaboration m =>
  MonadError UnificationError m =>
  UnificationTask ->
  m $ UnificationResult
unifyWithCompiler task = do
  let ret = runEitherT {m=Elab} {e=UnificationError} $ unify' task
  let err = pure {f=Elab} $ Left CatastrophicError
  rr <- try ret err
  dg <- liftEither rr
  -- logPoint {level=DetailedTrace} "unifyWithCompiler" [] "DG after trying: \{show dg}"
  let ur = finalizeDG task dg
  -- logPoint {level=DetailedTrace} "unifyWithCompiler" [] "Unification result: \{show ur}"
  pure ur

||| Run unification in a try block
export
unifyWithCompiler' :
  Elaboration m =>
  MonadError UnificationError m =>
  UnificationTask ->
  m $ UnificationResult
unifyWithCompiler' task = do
  rr <- runEitherT {m} {e=UnificationError} $ unify' task
  dg <- liftEither rr
  pure $ finalizeDG task dg

