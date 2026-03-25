module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin rc -> X rc

data Y : (f : (0 r : _) -> X r -> Fin r) -> X rc -> X rc -> Type where
  MkY : Y f (MkX (f rc x)) x

checkedGen : Fuel -> (rc : Nat) -> (f : (0 r : _) -> X r -> Fin r) -> (r1, r2 : X rc) -> Gen MaybeEmpty (Y f r1 r2)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

oneF : X rc -> Fin rc
oneF (MkX x) = x

Show (Y f a b) where
  show MkY = "MkY"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 5 (\_ => oneF) (MkX 0) (MkX 3)
  , G $ \fl => checkedGen fl 5 (\_ => oneF) (MkX 3) (MkX 3)
  ]
