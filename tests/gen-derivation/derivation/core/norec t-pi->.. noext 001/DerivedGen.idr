module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (a, b : Bool) -> Gen (a = b)
--checkedGen = deriveGen
checkedGen _ _ _ = empty

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl True True
  , G $ \fl => checkedGen fl True False
  , G $ \fl => checkedGen fl False True
  , G $ \fl => checkedGen fl False False
  ]
