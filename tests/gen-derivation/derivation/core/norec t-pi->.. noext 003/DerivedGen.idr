module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

-- isn't one of the arguments an index, not a param? Like for `Equal` type, recursively
data X : Bool -> Bool -> Type where
  MkX : (b1 : Bool) -> (b2 : Bool) -> (b1 = b2) -> X b1 b2

Show (X b1 b2) where
  show (MkX b1 b2 _) = "MkX \{show b1} \{show b2} Refl"

checkedGen : Fuel -> (b1 : Bool) -> (b2 : Bool) -> Gen MaybeEmpty (X b1 b2)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl True False
  , G $ \fl => checkedGen fl True True
  , G $ \fl => checkedGen fl False True
  , G $ \fl => checkedGen fl False False
  ]
