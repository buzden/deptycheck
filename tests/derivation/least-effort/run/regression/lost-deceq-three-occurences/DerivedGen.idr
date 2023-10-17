module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Nat -> Nat -> Type where
  MkX : X n n n

Show (X n m k) where
  show MkX = "MkX"

%language ElabReflection

checkedGen : Fuel -> (x1 : Nat) -> (x2 : Nat) -> (x3 : Nat) -> Gen MaybeEmpty $ X x1 x2 x3
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl Z Z Z
  ]
