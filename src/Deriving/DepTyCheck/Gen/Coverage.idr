||| Definitions and functions for working with model coverage of a bunch of generated values.
|||
||| Model coverage means a coverage in terms of the original data structure that is being generated,
||| e.g. involved types and their constructors.
module Deriving.DepTyCheck.Gen.Coverage

import Data.List
import Data.SortedMap

import Language.Reflection
import Language.Reflection.Types
import Language.Reflection.Syntax

import Deriving.DepTyCheck.Util.Reflection

import Test.DepTyCheck.Gen

%default total

export
record CoverageGenInfo (0 g : k) where
  constructor MkCoverageGenInfo
  types        : SortedMap String TypeInfo
  constructors : SortedMap String (TypeInfo, Con)
  coverageInfo : SortedMap TypeInfo (Bool, SortedMap Con Bool)

export %macro
initCoverageInfo : (0 x : g) -> Elab $ CoverageGenInfo x
initCoverageInfo _ = do
  genTy <- quote g
  let (_, genTy) = unPi genTy
  let (lhs, args) = unAppAny genTy
  let IVar _ lhsName = lhs
    | _ => failAt (getFC lhs) "Generator or generator function expected"
  let True = lhsName `nameConformsTo` `{Test.DepTyCheck.Gen.Gen}
    | _ => failAt (getFC lhs) "Return type must be a generator of some type"
  let [_, genTy] = args
    | _ => failAt (getFC lhs) "Wrong number of type arguments of a generator"
  let (_, IVar _ genTy) = unDPair $ getExpr genTy
    | (_, genTy) => failAt (getFC genTy) "Expected a type name"
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

export
Show (CoverageGenInfo g) where
  show cgi = joinBy "\n\n" $ SortedMap.toList cgi.coverageInfo <&> \(ti, tyCov, cons) => do
    let conCovs = values cons
    let anyCons = not $ null conCovs
    let allConsCovered = all (== True)  conCovs
    let noConsCovered  = all (== False) conCovs

    let tyCovStr = joinBy ", " $
                     (if tyCov then ["mentioned"] else ["not menioned"]) ++
                     (if anyCons then ["no constructors"]
                      else if allConsCovered then ["covered fully"]
                      else if noConsCovered then ["not covered"]
                      else ["covered partially"]
                     )
    joinBy "\n" $ (::) "\{show ti.name} \{tyCovStr}" $ whenTs anyCons $ map ("  - " ++) $
      SortedMap.toList cons <&> \(co, coCov) => "\{show co.name}: \{the String $ if coCov then "" else "not "} covered"

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
  registerCoverage1 : String -> CoverageGenInfo g -> CoverageGenInfo g
  registerCoverage1 str cgi = do
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
