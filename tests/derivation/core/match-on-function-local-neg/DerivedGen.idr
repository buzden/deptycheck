module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin rc -> X rc

data Y : (f : X rc -> Fin rc) -> X rc -> X rc -> Type where
  MkY : Y f (MkX (f x)) x

checkedGen : Fuel -> (rc : Nat) -> (r1, r2 : X rc) -> Gen MaybeEmpty (f ** Y f r1 r2)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (f ** Y f a b) where
  show (_ ** MkY) = "MkY"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 5 (MkX 0) (MkX 3)
  , G $ \fl => checkedGen fl 5 (MkX 3) (MkX 3)
  ]
