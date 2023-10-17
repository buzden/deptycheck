module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : {n : _} -> X n

Show (X n) where
  show $ MkX {n} = "MkX {n=\{show n}}"

data Y : Type where
  MkY : X n -> Y

Show Y where
  show $ MkY x = "MkY (\{show x})"

checkedGen : Fuel -> Gen MaybeEmpty Y
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
