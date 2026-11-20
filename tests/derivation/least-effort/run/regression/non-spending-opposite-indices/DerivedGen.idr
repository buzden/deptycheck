module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  L  : X n m
  C1 : X n (S m) -> X (S n) m
  C2 : X (S n) m -> X n (S m)

checkedGen : Fuel -> (n, m : Nat) -> Gen MaybeEmpty (X n m)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (X n m) where
  show x = "size \{show $ size x}" where
    size : forall n, m. X n m -> Nat
    size L      = 1
    size (C1 x) = 1 + size x
    size (C2 x) = 1 + size x

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0 0
  , G $ \fl => checkedGen fl 2 2
  , G $ \fl => checkedGen fl 5 0
  ]
