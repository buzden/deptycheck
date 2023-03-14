module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen0 b) => (Fuel -> Gen0 a) => Gen0 (a, b)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats}
  , G $ \fl => checkedGen fl @{smallNats} @{smallNats}
  ]
