module DerivedGen

import RunDerivedGen

%default total

data X : (Nat -> Nat) -> Type where
  Z : X S
  Y : X f -> X $ f . S

checkedGen : Fuel -> Gen MaybeEmpty (f ** X f)
checkedGen = deriveGen

Show (f ** X f) where
  show (f ** _) = "X being applied to Z is: \{show $ f Z}"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
