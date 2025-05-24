||| Definitions and functions for working with model coverage of a bunch of generated values.
|||
||| Model coverage means a coverage in terms of the original data structure that is being generated,
||| e.g. involved types and their constructors.
module Test.DepTyCheck.Gen.Coverage

import Control.Monad.Maybe
import Control.Monad.Random
import Control.Monad.Writer

import Data.Alternative
import Data.Fuel
import Data.List
import Data.List.Lazy
import Data.Singleton
import Data.SortedMap

import public Language.Reflection.Compat.TypeInfo
import public Language.Reflection.Logging

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
  manageLabel l = tell $ MkModelCoverage $ singleton l 1

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

mergeCovGenInfos : CoverageGenInfo g -> CoverageGenInfo g' -> CoverageGenInfo g''
mergeCovGenInfos (MkCoverageGenInfo ts cns cis) (MkCoverageGenInfo ts' cns' cis') =
  MkCoverageGenInfo (mergeLeft ts ts') (mergeLeft cns cns') (let _ : Semigroup Nat := Additive in cis <+> cis')

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
initCoverageInfo'' : (ns : List Name) -> Elab $ CoverageGenInfo ns
initCoverageInfo'' = go where
  go : (ns : List Name) -> Elab $ CoverageGenInfo ns
  go [] = fail "At least one name must be given"
  go [n] = coverageGenInfo n
  go (n::ns) = [| mergeCovGenInfos {g=n} (coverageGenInfo n) (go ns) |]

||| Returns a name by the generator's type
|||
||| Say, for the `Fuel -> Gen em (n ** Fin n)` it returns name of `Data.Fin.Fin`
genTypeName : (0 _ : Type) -> Elab Name
genTypeName g = do
  genTy <- quote g
  let (_, genTy) = unPi genTy
  let (lhs, args) = unAppAny genTy
  let IVar _ lhsName = lhs
    | _ => failAt (getFC lhs) "Generator or generator function expected"
  let True = lhsName `nameConformsTo` `{Test.DepTyCheck.Gen.Gen}
    | _ => failAt (getFC lhs) "Return type must be a generator of some type"
  let [_, genTy] = args
    | _ => failAt (getFC lhs) "Wrong number of type arguments of a generator"
  let (_, genTy) = unDPair $ getExpr genTy
  let (IVar _ genTy, _) = unAppAny genTy
    | (genTy, _) => failAt (getFC genTy) "Expected a type name, got \{show genTy}"
  pure genTy

export %macro
initCoverageInfo : (0 x : g) -> Elab $ CoverageGenInfo x
initCoverageInfo _ = genTypeName g >>= coverageGenInfo

||| Derives function `A -> B` where `A` is determined by the given `TypeInfo`, `B` is determined by `retTy`
|||
||| For each constructor of `A` the `matcher` function is applied and its result (of type `B`) is used as a result.
||| Currently, `B` must be a non-dependent type.
deriveMatchingCons : (retTy : TTImp) -> (matcher : Con -> TTImp) -> (funName : Name) -> TypeInfo -> List Decl
deriveMatchingCons retTy matcher funName ti = do
  let claim = do
    let tyApplied = reAppAny (var ti.name) $ ti.args <&> \arg => appArg arg $ var $ argName arg
    let sig = foldr
                (pi . {count := M0, piInfo := ImplicitArg})
                `(~tyApplied -> ~retTy)
                ti.args
    private' funName sig
  let body = do
    let matchCon = \con => reAppAny (var con.name) $ con.args <&> flip appArg implicitTrue
    def funName $ ti.cons <&> \con =>
      patClause (var funName .$ matchCon con) $ matcher con
  [claim, body]

||| Adds labelling of types and constructors to a given generator
|||
||| Added labelling is not deep, i.e. it adds labels only for the returned type of a generator.
||| If returned type is a dependent pair, the rightmost type is taken into the account.
export %macro
withCoverage : {em : _} -> (gen : Gen em a) -> Elab $ Gen em a
withCoverage gen = do
  tyExpr <- quote a
  let (dpairLefts, tyRExpr) = unDPair tyExpr
  let (IVar _ tyName, _) = unAppAny tyRExpr
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
                         (var labellingFunName .$ var undpairedVal))
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
