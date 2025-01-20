module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : String -> Nat -> Type where
  MkX : (n : _) -> (m : _) -> X n m

Show (X n m) where
  show $ MkX n m = "MkX \{show n} \{show m}"

data Y : Nat -> Type where
  MkY : forall n, m, k. let xx : Nat -> Nat; xx = S in X n (xx m) -> X n (xx k) -> Y (xx m)

Show (Y n) where
  show $ MkY xnm xnk = "MkY (\{show xnm}) (\{show xnk})"

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => (n : Nat) -> Gen MaybeEmpty $ Y n
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} 4
  ]
