module DerivedGen

import RunDerivedGen

import Data.Fin

import Deriving.Show

%default total

data X : Int32 -> Type where
  X1  : X 1
  X2  : X 2
  X2' : X 2

data Y : X 2 -> Type where
  MkY : Y X2

%language ElabReflection

checkedGen : Fuel -> (x : _) -> Gen MaybeEmpty (Y x)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

%hint ShowY : Show (Y x); ShowY = %runElab derive

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl X2
  , G $ \fl => checkedGen fl X2'
  ]
