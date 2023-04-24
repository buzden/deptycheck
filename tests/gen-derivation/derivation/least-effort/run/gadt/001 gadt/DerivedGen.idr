module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

checkedGen : Fuel -> (n : Nat) -> Gen CanBeEmptyStatic $ Fin n
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 1
  , G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 5
  ]
