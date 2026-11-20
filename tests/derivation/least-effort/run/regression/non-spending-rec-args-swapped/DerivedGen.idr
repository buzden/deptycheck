module DerivedGen

import RunDerivedGen

%default total

data Ty = Base | Arr Ty Ty

data X : Ty -> Ty -> Type where
  SBase : X Base Base
  SArr  : X c a -> X b d -> X (Arr a b) (Arr c d)

checkedGen : Fuel -> (a, b : Ty) -> Gen MaybeEmpty (X a b)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (X a b) where
  show x = "size \{show $ size x}" where
    size : forall a, b. X a b -> Nat
    size SBase      = 1
    size (SArr l r) = 1 + size l + size r

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl Base Base
  , G $ \fl => checkedGen fl (Arr Base Base) (Arr Base Base)
  , G $ \fl => checkedGen fl (Arr (Arr Base Base) Base) (Arr (Arr Base Base) Base)
  ]
