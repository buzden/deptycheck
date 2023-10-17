module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Nat -> Nat -> Nat -> Type where
  MkX : X n n n n

Show (X n m k l) where
  show MkX = "MkX"

%language ElabReflection

checkedGen : Fuel -> (x1 : Nat) -> (x2 : Nat) -> (x3 : Nat) -> (x4 : Nat) -> Gen MaybeEmpty $ X x1 x2 x3 x4
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl Z Z Z Z
  ]
