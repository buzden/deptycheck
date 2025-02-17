module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

data Y : Int32 -> Type where
  MkY : Y 1

%language ElabReflection

checkedGen : Fuel -> (x : _) -> Gen MaybeEmpty (Y x)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

%hint ShowY : Show (Y x); ShowY = %runElab derive

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 1
  , G $ \fl => checkedGen fl 2147483647 -- 2 ** 31 - 1
  , G $ \fl => checkedGen fl (-1)
  ]
