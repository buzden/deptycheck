module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen b) => (Fuel -> Gen a) => Gen (a, b)
--checkedGen = deriveGen
checkedGen _ = empty

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats}
  , G $ \fl => checkedGen fl @{smallNats} @{smallNats}
  ]
