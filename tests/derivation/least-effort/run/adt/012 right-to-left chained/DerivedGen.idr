module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X1 : Nat -> Type where
  MkX1 : (n : _) -> X1 n

Show (X1 n) where
  show $ MkX1 n = "MkX1 \{show n}"

data X2 : Nat -> Type where
  MkX2 : (n : _) -> X1 n -> X2 n

Show (X2 n) where
  show $ MkX2 n x1 = "MkX \{show n} (\{show x1})"

data Y : Type where
  MkY : X2 n -> Y

Show Y where
  show $ MkY x2 = "MkY (\{show x2})"

checkedGen : Fuel -> Gen MaybeEmpty Y
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
