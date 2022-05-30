module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

checkedGen : Fuel -> (a, b : Type) -> (Fuel -> Gen a) => (Fuel -> Gen b) => Gen (a, b)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl Nat    Nat @{smallNats} @{smallNats}
  , G $ \fl => checkedGen fl String Nat @{smallStrs} @{smallNats}
  ]
