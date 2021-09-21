module DerivedGen

import RunDerivedGen

%default total

export
checkedGen : Fuel -> (a, b : Nat) -> Gen (a = b)
--checkedGen = deriveGen
checkedGen _ _ _ = empty

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0 0
  , G $ \fl => checkedGen fl 0 1
  , G $ \fl => checkedGen fl 18 18
  , G $ \fl => checkedGen fl 18 0
  , G $ \fl => checkedGen fl 18 17
  ]
