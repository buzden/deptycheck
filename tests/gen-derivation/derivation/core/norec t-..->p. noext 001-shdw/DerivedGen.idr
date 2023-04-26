module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

-- same as test `001`, but
-- names inside consturctor are the same as in the type itself;
-- this exploits a bug of bad renaming during the `quote` of a type
data X : (b1 : Bool) -> (b2 : Bool) -> Type where
  MkX : (b1 : Bool) -> (b2 : Bool) -> X b1 b2

Show (X b1 b2) where
  show (MkX b1 b2) = "MkX \{show b1} \{show b2}"

checkedGen : Fuel -> (b1 : Bool) -> (b2 : Bool) -> Gen MaybeEmpty (X b1 b2)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl True False
  , G $ \fl => checkedGen fl True True
  , G $ \fl => checkedGen fl False True
  , G $ \fl => checkedGen fl False False
  ]
