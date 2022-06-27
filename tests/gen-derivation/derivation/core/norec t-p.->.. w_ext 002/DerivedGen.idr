module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> {a, b : _} -> (Fuel -> Gen b) => (Fuel -> Gen a) => Gen (a, b)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats}
  , G $ \fl => checkedGen fl @{smallNats} @{smallNats}
  ]
