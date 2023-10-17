module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

{n : Nat} -> Show (X n) where
  show MkX = "MkX : X \{show n}"

data Y : Type where
  MkY : {n : _} -> X n -> Y

Show Y where
  show $ MkY {n} x = "MkY {n=\{show n}} (\{show x})"

checkedGen : Fuel -> Gen MaybeEmpty Y
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
