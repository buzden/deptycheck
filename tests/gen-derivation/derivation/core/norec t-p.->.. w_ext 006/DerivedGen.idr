module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X a b = MkX (Maybe (a, b, a))

Show a => Show b => Show (X a b) where
  show (MkX m) = "MkX \{show m}"

checkedGen : Fuel -> (Fuel -> Gen CanBeEmptyStatic a) => (Fuel -> Gen CanBeEmptyStatic b) => Gen CanBeEmptyStatic (X a b)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats}
  , G $ \fl => checkedGen fl @{smallNats} @{smallNats}
  ]
