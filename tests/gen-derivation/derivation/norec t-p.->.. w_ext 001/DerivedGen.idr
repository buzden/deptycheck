module DerivedGen

import RunDerivedGen

%default total

checkedGen : Fuel -> (Fuel -> Gen a) => Gen (Maybe a)
--checkedGen = deriveGen
checkedGen _ = empty

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrings}
  , G $ \fl => checkedGen fl @{smallNats}
  ]
