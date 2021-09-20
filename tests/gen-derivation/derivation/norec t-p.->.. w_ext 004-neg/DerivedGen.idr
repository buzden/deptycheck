module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen a) => (Fuel -> Gen b) => Gen (a, b, a)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrings} @{smallNats}
  , G $ \fl => checkedGen fl @{smallNats} @{smallNats}
  ]
