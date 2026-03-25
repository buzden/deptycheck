module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin rc -> X rc

data Y : (f : X rc -> Fin rc) -> X rc -> X rc -> Type where
  MkY : Y f (MkX (f x)) x

checkedGen : Fuel -> (rc : Nat) -> (f : X rc -> Fin rc) -> (r1, r2 : X rc) -> Gen MaybeEmpty (Y f r1 r2)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

oneF : X rc -> Fin rc
oneF (MkX x) = x

Show (Y f a b) where
  show MkY = "MkY"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 5 oneF (MkX 0) (MkX 3)
  , G $ \fl => checkedGen fl 5 oneF (MkX 3) (MkX 3)
  ]
