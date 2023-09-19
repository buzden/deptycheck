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
  let cov  = fromList $ involvedTypes <&> \ty => (ty, (False, fromList $ ty.cons <&> (, False)))
  let tys  = fromList $ involvedTypes <&> \ty => (show ty.name, ty)
  let cons = fromList $ (involvedTypes >>= \ty => (ty,) <$> ty.cons) <&> \(ty, co) => (show co.name, (ty, co))
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
  let (IVar _ genTy, _) = unApp genTy
    | (genTy, _) => failAt (getFC genTy) "Expected a type name"
  pure genTy

export %macro
initCoverageInfo : (0 x : g) -> Elab $ CoverageGenInfo x
initCoverageInfo _ = genTypeName g >>= coverageGenInfo

export
Show (CoverageGenInfo g) where
  show cgi = joinBy "\n\n" $ SortedMap.toList cgi.coverageInfo <&> \(ti, tyCov, cons) => do
    let conCovs = values cons
    let anyCons = not $ null conCovs
    let allConsCovered = all (== True)  conCovs
    let noConsCovered  = all (== False) conCovs

    let tyCovStr = joinBy ", " $
                     (if tyCov && noConsCovered then ["mentioned"]
                      else if not tyCov && (not anyCons || not noConsCovered) then ["not menioned"]
                      else []) ++
                     (if not anyCons then ["no constructors"]
                      else if allConsCovered then ["covered fully"]
                      else if noConsCovered then ["not covered"]
                      else ["covered partially"]
                     )
    joinBy "\n" $ (::) "\{show ti.name} \{tyCovStr}" $ whenTs anyCons $ map ("  - " ++) $
      SortedMap.toList cons <&> \(co, coCov) => "\{logPosition co}: \{the String $ if coCov then "" else "not "}covered"

infixOf : Eq a => List a -> List a -> Maybe (List a, List a)
infixOf = map (map snd) .: infixOfBy (\x, y => if x == y then Just () else Nothing)

update : (v -> v) -> k -> SortedMap k v -> SortedMap k v
update f k m = do
  let Just v = lookup k m
    | Nothing => m
  insert k (f v) m

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
                  Just ti => { coverageInfo $= update (mapFst $ const True) ti }
                  Nothing => id
    -- Try constructor
    let co = maybe str (fastPack . fst) $ fastUnpack " " `infixOf` str'
    let coMod : (_ -> CoverageGenInfo g) := case lookup co cgi.constructors of
                  Just (ti, co) => { coverageInfo $= update (mapSnd $ insert co True) ti }
                  Nothing       => id
    tyMod $ coMod $ cgi
