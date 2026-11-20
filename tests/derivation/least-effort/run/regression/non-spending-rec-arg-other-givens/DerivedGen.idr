module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  L : X n m
  N : X n k -> X (S n) m

checkedGen : Fuel -> (n, m : Nat) -> Gen MaybeEmpty (X n m)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (X n m) where
  show x = "size \{show $ size x}" where
    size : forall n, m. X n m -> Nat
    size L     = 1
    size (N x) = 1 + size x

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0 0
  , G $ \fl => checkedGen fl 2 2
  , G $ \fl => checkedGen fl 5 0
  ]
