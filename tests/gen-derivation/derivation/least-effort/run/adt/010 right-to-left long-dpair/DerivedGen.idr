module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {n : _} -> {m : _} -> X n m

Show (X n m) where
  show $ MkX {n} {m} = "MkX {n=\{show n}} {m=\{show m}}"

data Y : Type where
  MkY : X n m -> Y

Show Y where
  show $ MkY x = "MkY (\{show x})"

checkedGen : Fuel -> Gen Y
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
