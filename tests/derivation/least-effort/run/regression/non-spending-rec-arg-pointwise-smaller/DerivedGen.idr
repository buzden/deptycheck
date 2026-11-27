module DerivedGen

import RunDerivedGen

%default total

data Ty = NatTy | VecTy Nat Ty

data X : Ty -> Type where
  VNat  : Nat -> X NatTy
  VNil  : X (VecTy 0 a)
  VCons : X a -> X (VecTy n a) -> X (VecTy (S n) a)

checkedGen : Fuel -> (t : Ty) -> Gen MaybeEmpty (X t)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (X t) where
  show x = "size \{show $ size x}" where
    size : forall t. X t -> Nat
    size (VNat _)    = 1
    size VNil        = 1
    size (VCons x v) = 1 + size x + size v

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl NatTy
  , G $ \fl => checkedGen fl (VecTy 3 NatTy)
  , G $ \fl => checkedGen fl (VecTy 2 $ VecTy 2 NatTy)
  ]
