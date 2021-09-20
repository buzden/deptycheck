module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X a b = MkX (Maybe (a, b, a))

Show a => Show b => Show (X a b) where
  show (MkX m) = "MkX \{show m}"

checkedGen : Fuel -> (Fuel -> Gen a) => (Fuel -> Gen b) => Gen (X a b)
--checkedGen = deriveGen
checkedGen _ = empty

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrings} @{smallNats}
  , G $ \fl => checkedGen fl @{smallNats} @{smallNats}
  ]
