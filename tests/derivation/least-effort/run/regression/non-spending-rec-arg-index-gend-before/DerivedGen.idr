module DerivedGen

import RunDerivedGen

%default total

data Tag = A | B

data W = MkW Tag

data X : Nat -> W -> Type where
  L : X n w
  N : X (S n) (MkW t) -> X n w -> X (S n) w

checkedGen : Fuel -> (n : Nat) -> (w : W) -> Gen MaybeEmpty (X n w)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (X n w) where
  show x = "size \{show $ size x}" where
    size : forall n, w. X n w -> Nat
    size L       = 1
    size (N l r) = 1 + size l + size r

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0 (MkW A)
  , G $ \fl => checkedGen fl 1 (MkW B)
  , G $ \fl => checkedGen fl 3 (MkW A)
  ]
