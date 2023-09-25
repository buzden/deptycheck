||| Definitions and functions for working with model coverage of a bunch of generated values.
|||
||| Model coverage means a coverage in terms of the original data structure that is being generated,
||| e.g. involved types and their constructors.
module Test.DepTyCheck.Gen.Coverage

import Control.ANSI

import Control.Monad.Maybe
import Control.Monad.Random
import Control.Monad.Writer

import Data.List
import Data.Singleton
import Data.SortedMap

import public Deriving.DepTyCheck.Util.Logging
import public Deriving.DepTyCheck.Util.Reflection

import public Language.Reflection
import public Language.Reflection.Types
import public Language.Reflection.Syntax

import Test.DepTyCheck.Gen

%default total

export
record ModelCoverage where
  constructor MkModelCoverage
  unModelCoverage : SortedSet Label

export
Semigroup ModelCoverage where
  (<+>) = MkModelCoverage .: (<+>) `on` unModelCoverage

export
Monoid ModelCoverage where
  neutral = MkModelCoverage neutral

MonadWriter ModelCoverage m => CanManageLabels m where
  manageLabel l x = tell (MkModelCoverage $ singleton l) >> x

export
unGenTryAllD : RandomGen g => (seed : g) -> Gen em a -> Stream $ Maybe (ModelCoverage, a)
unGenTryAllD seed gen = do
  let (seed, sv) = runRandom seed $ runMaybeT $ runWriterT $ unGen {m=WriterT ModelCoverage $ MaybeT Rand} gen
  map swap sv :: unGenTryAllD seed gen

export
unGenTryND : RandomGen g => (n : Nat) -> g -> Gen em a -> LazyList (ModelCoverage, a)
unGenTryND n = mapMaybe id .: take (limit n) .: unGenTryAllD

export
record CoverageGenInfo (0 g : k) where
  constructor MkCoverageGenInfo
  types        : SortedMap String TypeInfo
  constructors : SortedMap String (TypeInfo, Con)
  coverageInfo : SortedMap TypeInfo (Bool, SortedMap Con Bool)

coverageGenInfo : Name -> Elab $ CoverageGenInfo x
coverageGenInfo genTy = do
  involvedTypes <- allInvolvedTypes =<< getInfo' genTy
  let cov  = fromList $ involvedTypes <&> \ty => (ty, False, fromList $ ty.cons <&> (, False))
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
toString col cgi = joinBy "\n\n" $ mapMaybe (\ti => lookup ti cgi.coverageInfo <&> (ti,)) (SortedMap.values cgi.types) <&> \(ti, tyCov, cons) => do
  let conCovs = values cons
  let anyCons = not $ null conCovs
  let allConsCovered = all (== True)  conCovs
  let noConsCovered  = all (== False) conCovs

  let c = c col
  let tyCovStr = joinBy ", " $
                   (if tyCov && noConsCovered then [c BrightYellow "mentioned"]
                    else if not tyCov && (not anyCons || not noConsCovered) then [c BrightYellow "not menioned"]
                    else []) ++
                   (if not anyCons then [c Cyan "no constructors"]
                    else if allConsCovered then [c BrightGreen "covered fully"]
                    else if noConsCovered then [c BrightRed "not covered"]
                    else [c BrightYellow "covered partially"]
                   )
  joinBy "\n" $ (::) "\{showType col ti} \{tyCovStr}" $ whenTs anyCons $ map ("  - " ++) $
    SortedMap.toList cons <&> \(co, coCov) => do
      let status : String := if coCov then c BrightGreen "covered" else c BrightRed "not covered"
      "\{logPosition co}: \{status}"

export
Show (CoverageGenInfo g) where show = toString False

export
[Colourful] Show (CoverageGenInfo g) where show = toString True

export
registerCoverage : ModelCoverage -> CoverageGenInfo g -> CoverageGenInfo g
registerCoverage mc cgi = foldr registerCoverage1 cgi mc.unModelCoverage where
  registerCoverage1 : Label -> CoverageGenInfo g -> CoverageGenInfo g
  registerCoverage1 str cgi = do
    let str = show str
    let str' = fastUnpack str
    -- Try type
    let ty = maybe str (fastPack . fst) $ fastUnpack "[" `infixOf` str'
    let tyMod = case lookup ty cgi.types of
                  Just ti => { coverageInfo $= updateExisting (mapFst $ const True) ti }
                  Nothing => id
    -- Try constructor
    let co = maybe str (fastPack . fst) $ fastUnpack " " `infixOf` str'
    let coMod : (_ -> CoverageGenInfo g) := case lookup co cgi.constructors of
                  Just (ti, co) => { coverageInfo $= updateExisting (mapSnd $ insert co True) ti }
                  Nothing       => id
    tyMod $ coMod $ cgi
