module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : String -> Nat -> Type where
  MkX : (n : _) -> (m : _) -> X n m

Show (X n m) where
  show $ MkX n m = "MkX \{show n} \{show m}"

data Y : Type where
  MkY : X n m -> X n k -> Y

Show Y where
  show $ MkY xnm xnk = "MkY (\{show xnm}) (\{show xnk})"

checkedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen Y
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats}
  ]
