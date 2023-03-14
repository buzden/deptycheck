module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

{n : Nat} -> Show (X n) where
  show MkX = "MkX : X \{show n}"

checkedGen : Fuel -> Gen0 (n ** X n)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
