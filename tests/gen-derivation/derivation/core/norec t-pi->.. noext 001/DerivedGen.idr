module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data BoolEq : Bool -> Bool -> Type where
  MkBoolEq : a === b -> BoolEq a b

Show (BoolEq a b) where
  show _ = "Refl"

checkedGen : Fuel -> (a, b : Bool) -> Gen (BoolEq a b) -- Gen (a = b)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl True True
  , G $ \fl => checkedGen fl True False
  , G $ \fl => checkedGen fl False True
  , G $ \fl => checkedGen fl False False
  ]
