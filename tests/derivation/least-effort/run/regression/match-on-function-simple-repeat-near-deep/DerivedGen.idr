module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin rc -> Fin (S rc) -> X rc

namespace F
  export
  f : X rc -> Fin rc
  f (MkX x FZ) = x
  f (MkX x $ FS y) = x `max` y

data Y : X rc -> X rc -> Type where
  MkY : Y (MkX (f x) (FS $ f x)) x

checkedGen : Fuel -> (rc : Nat) -> (r1, r2 : X rc) -> Gen MaybeEmpty (Y r1 r2)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (Y a b) where
  show MkY = "MkY"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 5 (MkX 0 1) (MkX 3 0)
  , G $ \fl => checkedGen fl 5 (MkX 3 4) (MkX 3 0)
  , G $ \fl => checkedGen fl 5 (MkX 0 0) (MkX 0 0)
  , G $ \fl => checkedGen fl 5 (MkX 0 1) (MkX 0 0)
  ]
