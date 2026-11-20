module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Type where
  L : X n
  N : X n -> X (S n) -> X (S n)

checkedGen : Fuel -> (n : Nat) -> Gen MaybeEmpty (X n)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (X n) where
  show x = "size \{show $ size x}" where
    size : forall n. X n -> Nat
    size L       = 1
    size (N l r) = 1 + size l + size r

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 1
  , G $ \fl => checkedGen fl 3
  ]
