module DerivedGen

import RunDerivedGen

%default total

data X : Nat -> Type where
  Leaf : X 0
  Bal  : X n -> X n -> X (S n)
  LH   : X (S n) -> X n -> X (S (S n))
  RH   : X n -> X (S n) -> X (S (S n))

checkedGen : Fuel -> (n : Nat) -> Gen MaybeEmpty (X n)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (X n) where
  show x = "size \{show $ size x}" where
    size : forall n. X n -> Nat
    size Leaf      = 1
    size (Bal l r) = 1 + size l + size r
    size (LH l r)  = 1 + size l + size r
    size (RH l r)  = 1 + size l + size r

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 2
  , G $ \fl => checkedGen fl 5
  ]
