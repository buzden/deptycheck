module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X a = MkX (Maybe (a, a))

Show a => Show (X a) where
  show (MkX m) = "MkX \{show m}"

checkedGen : Fuel -> (Fuel -> Gen a) => Gen (X a)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs}
  , G $ \fl => checkedGen fl @{smallNats}
  ]
