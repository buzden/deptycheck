module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

checkedGen : Fuel -> (a : Type) -> (Fuel -> Gen a) => Gen $ Maybe a
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl Nat    @{smallNats}
  , G $ \fl => checkedGen fl String @{smallStrs}
  ]
