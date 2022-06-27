module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> {a : _} -> (Fuel -> Gen a) => Gen (Maybe a)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs}
  , G $ \fl => checkedGen fl @{smallNats}
  ]
