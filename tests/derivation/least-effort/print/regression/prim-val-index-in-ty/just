module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X = MkX Int32

data Y : X -> Type where
  MkY : Y (MkX 1)

%language ElabReflection

checkedGen : Fuel -> (x : _) -> Gen MaybeEmpty (Y x)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl (MkX 1)
  , G $ \fl => checkedGen fl (MkX 2147483647)  -- 2 ** 31 - 1
  , G $ \fl => checkedGen fl (MkX -1)
  ]
