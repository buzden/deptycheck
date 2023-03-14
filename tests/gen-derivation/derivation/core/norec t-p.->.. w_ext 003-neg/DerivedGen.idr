module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen0 a) => Gen0 (a, a)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs}
  , G $ \fl => checkedGen fl @{smallNats}
  ]
