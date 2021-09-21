module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen a) => Gen (a, a)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs}
  , G $ \fl => checkedGen fl @{smallNats}
  ]
