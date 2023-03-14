module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen0 a) => (Fuel -> Gen0 b) => Gen0 (a, b, a)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats}
  , G $ \fl => checkedGen fl @{smallNats} @{smallNats}
  ]
