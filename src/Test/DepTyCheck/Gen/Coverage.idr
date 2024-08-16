||| Definitions and functions for working with model coverage of a bunch of generated values.
|||
||| Model coverage means a coverage in terms of the original data structure that is being generated,
||| e.g. involved types and their constructors.
module Test.DepTyCheck.Gen.Coverage

import Control.Monad.Maybe
import Control.Monad.Random
import Control.Monad.Writer

import Data.List
import Data.Singleton
import Data.SortedMap

import public Deriving.DepTyCheck.Util.Logging
import public Deriving.DepTyCheck.Util.Reflection

import public Language.Reflection

import Test.DepTyCheck.Gen

import Text.ANSI

%default total

||| Raw information of covered labels
public export
record ModelCoverage where
  constructor MkModelCoverage
  unModelCoverage : SortedMap Label Nat

export
Semigroup ModelCoverage where
  (<+>) = MkModelCoverage .: mergeWith (+) `on` unModelCoverage

export
Monoid ModelCoverage where
  neutral = MkModelCoverage empty

MonadWriter ModelCoverage m => CanManageLabels m where
  manageLabel l x = tell (MkModelCoverage $ singleton l 1) >> x

export
unGenD : MonadRandom m => MonadError () m => Gen em a -> m (ModelCoverage, a)
unGenD = map swap . runWriterT . unGen {m = WriterT ModelCoverage $ m}

export %inline
unGenD' : MonadRandom m => Gen em a -> m $ Maybe (ModelCoverage, a)
unGenD' = runMaybeT . unGenD {m = MaybeT m}

export
unGenTryAllD' : RandomGen g => (seed : g) -> Gen em a -> Stream (g, Maybe (ModelCoverage, a))
unGenTryAllD' seed gen = do
  let (seed, sv) = runRandom seed $ runMaybeT $ runWriterT $ unGen {m=WriterT ModelCoverage $ MaybeT Rand} gen
  (seed, map swap sv) :: unGenTryAllD' seed gen

export
unGenTryAllD : RandomGen g => (seed : g) -> Gen em a -> Stream $ Maybe (ModelCoverage, a)
unGenTryAllD = map snd .: unGenTryAllD'

export
unGenTryND : RandomGen g => (n : Nat) -> g -> Gen em a -> LazyList (ModelCoverage, a)
unGenTryND n = mapMaybe id .: take (limit n) .: unGenTryAllD

||| Higher-level coverage information, in terms of types and constructors, etc.
export
record CoverageGenInfo (0 g : k) where
  constructor MkCoverageGenInfo
  types        : SortedMap String TypeInfo
  constructors : SortedMap String (TypeInfo, Con)
  coverageInfo : SortedMap TypeInfo (Nat, SortedMap Con Nat)

coverageGenInfo : Name -> Elab $ CoverageGenInfo x
coverageGenInfo genTy = do
  involvedTypes <- allInvolvedTypes MW =<< getInfo' genTy
  let cov  = fromList $ involvedTypes <&> \ty => (ty, 0, fromList $ ty.cons <&> (, 0))
  let tys  = fromList $ involvedTypes <&> \ty => (show ty.name, ty)
  let cons = fromList $ (involvedTypes >>= \ty => (ty,) <$> ty.cons) <&> \(ty, co) => (show co.name, ty, co)
  pure $ MkCoverageGenInfo tys cons cov

  where
    Eq TypeInfo where
      (==) = (==) `on` name

    Ord TypeInfo where
      compare = comparing name

    Eq Con where
      (==) = (==) `on` name

    Ord Con where
      compare = comparing name

export %macro
initCoverageInfo' : (n : Name) -> Elab $ CoverageGenInfo n
initCoverageInfo' n = coverageGenInfo n

export %macro
initCoverageInfo : (0 x : g) -> Elab $ CoverageGenInfo x
initCoverageInfo _ = genTypeName g >>= coverageGenInfo

||| Adds labelling of types and constructors to a given generator
|||
||| Added labelling is not deep, i.e. it adds labels only for the returned type of a generator.
||| If returned type is a dependent pair, the rightmost type is taken into the account.
export %macro
withCoverage : {em : _} -> (gen : Gen em a) -> Elab $ Gen em a
withCoverage gen = do
  tyExpr <- quote a
  let (dpairLefts, tyRExpr) = unDPair tyExpr
  let (IVar _ tyName, _) = unApp tyRExpr
    | (genTy, _) => failAt (getFC genTy) "Expected a normal type name"
  tyInfo <- getInfo' tyName
  let matchDPair = \expr => foldr (\_, r => var "Builtin.DPair.MkDPair" .$ implicitTrue .$ r) expr dpairLefts
  let tyLabelStr = "\{show tyName}[?]"
  let labelledValName = UN $ Basic "^val^"
  let labellingFunName = UN $ Basic "^labelling^"
  let undpairedVal = "^undpaired^"
  let consLabellingFun = deriveMatchingCons
                           `(Test.DepTyCheck.Gen.Labels.Label)
                           (\con => var "fromString" .$ primVal (Str $ "\{show con.name} (user-defined)"))
                           labellingFunName tyInfo
  labeller <- check $ lam (lambdaArg labelledValName) $
                local consLabellingFun $
                  `(Test.DepTyCheck.Gen.label
                     ~(iCase (var labelledValName) implicitTrue $ pure $
                       patClause
                         (matchDPair $ bindVar undpairedVal)
                         (var labellingFunName .$ varStr undpairedVal))
                     (pure ~(var labelledValName)))
  pure $ label (fromString tyLabelStr) $ gen >>= labeller

c : (colourful : Bool) -> Color -> String -> String
c False _   = id
c True  col = show . colored col

||| Boldens the rightmost name after the last dot, if coloured
showType : (colourful : Bool) -> TypeInfo -> String
showType False ti = show ti.name
showType True  ti = joinBy "." $ forget $ uncurry lappend $ map (singleton . show . bolden) $ unsnoc $ split (== '.') $ show ti.name

toString : (colourful : Bool) -> CoverageGenInfo g -> String
toString col cgi = (++ "\n") $ joinBy "\n\n" $
                     mapMaybe (\ti => lookup ti cgi.coverageInfo <&> (ti,)) (SortedMap.values cgi.types) <&> \(ti, tyCovCnt, cons) => do
  let conCovs = values cons
  let anyCons = not $ null conCovs
  let allConsCovered = all (/= 0) conCovs
  let noConsCovered  = all (== 0) conCovs

  let c = c col
  let cntAddition = \cnt : Nat => " (\{show cnt} time\{if cnt /= 1 then "s" else ""})"
  let tyCovStr = joinBy ", " $
                   (if tyCovCnt /= 0 && noConsCovered then [c BrightYellow "mentioned" ++ cntAddition tyCovCnt]
                    else if tyCovCnt == 0 && (not anyCons || not noConsCovered) then [c BrightYellow "not menioned"]
                    else []) ++
                   (if not anyCons then [c Cyan "no constructors"]
                    else if allConsCovered then [c BrightGreen "covered fully" ++ cntAddition tyCovCnt]
                    else if noConsCovered then [c BrightRed "not covered"]
                    else [c BrightYellow "covered partially" ++ cntAddition tyCovCnt]
                   )
  joinBy "\n" $ (::) "\{showType col ti} \{tyCovStr}" $ whenTs anyCons $ map ("  - " ++) $
    SortedMap.toList cons <&> \(co, coCovCnt) => do
      let status : String := if coCovCnt /= 0 then c BrightGreen "covered" ++ cntAddition coCovCnt else c BrightRed "not covered"
      "\{logPosition co}: \{status}"

export
Show (CoverageGenInfo g) where show = toString False

export
[Colourful] Show (CoverageGenInfo g) where show = toString True

export
registerCoverage : ModelCoverage -> CoverageGenInfo g -> CoverageGenInfo g
registerCoverage mc cgi = foldr registerCoverage1 cgi $ toList mc.unModelCoverage where
  registerCoverage1 : (Label, Nat) -> CoverageGenInfo g -> CoverageGenInfo g
  registerCoverage1 (str, cnt) cgi = do
    let str = show str
    let str' = fastUnpack str
    -- Try type
    let ty = maybe str (fastPack . fst) $ fastUnpack "[" `infixOf` str'
    let tyMod = case lookup ty cgi.types of
                  Just ti => { coverageInfo $= flip updateExisting ti $ mapFst (+cnt) }
                  Nothing => id
    -- Try constructor
    let co = maybe str (fastPack . fst) $ fastUnpack " " `infixOf` str'
    let coMod : (_ -> CoverageGenInfo g) := case lookup co cgi.constructors of
                  Just (ti, co) => { coverageInfo $= flip updateExisting ti $ mapSnd $ updateExisting (+cnt) co }
                  Nothing       => id
    tyMod $ coMod $ cgi
