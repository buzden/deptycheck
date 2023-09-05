||| Definitions and functions for working with model coverage of a bunch of generated values.
|||
||| Model coverage means a coverage in terms of the original data structure that is being generated,
||| e.g. involved types and their constructors.
module Deriving.DepTyCheck.Gen.Coverage

import Data.SortedMap

import Language.Reflection
import Language.Reflection.Types
import Language.Reflection.Syntax

import Deriving.DepTyCheck.Util.Reflection

import Test.DepTyCheck.Gen

%default total

export
record CoverageGenInfo g where
  constructor MkCoverageGenInfo
  involvedTypesAndCons : SortedMap TypeInfo $ List Con

export %macro
coverageGenInfo : (0 x : g) -> Elab $ CoverageGenInfo x
coverageGenInfo _ = do
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
  tyInfo <- getInfo' genTy
  involvedTypes <- allInvolvedTypes tyInfo
  pure $ MkCoverageGenInfo $ fromList $ involvedTypes <&> map cons . dup

  where
    Eq TypeInfo where
      (==) = (==) `on` name

    Ord TypeInfo where
      compare = comparing name

export
showModelCoverage : CoverageGenInfo g -> ModelCoverage -> String
