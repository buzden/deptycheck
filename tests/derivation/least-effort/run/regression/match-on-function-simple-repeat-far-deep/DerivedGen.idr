module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin rc -> X rc

namespace F
  export
  f : X rc -> Fin rc
  f (MkX x) = x

data Y : X rc -> X (S rc) -> X rc -> Type where
  MkY : Y (MkX $ f x) (MkX $ FS $ f x) x

checkedGen : Fuel -> (rc : Nat) -> (r1 : X rc) -> (r2 : X $ S rc) -> (r3 : X rc) -> Gen MaybeEmpty (Y r1 r2 r3)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (Y a b c) where
  show MkY = "MkY"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 5 (MkX 0) (MkX 0) (MkX 3)
  , G $ \fl => checkedGen fl 5 (MkX 0) (MkX 1) (MkX 3)
  , G $ \fl => checkedGen fl 5 (MkX 0) (MkX 4) (MkX 3)
  , G $ \fl => checkedGen fl 5 (MkX 3) (MkX 3) (MkX 3)
  , G $ \fl => checkedGen fl 5 (MkX 3) (MkX 4) (MkX 3)
  , G $ \fl => checkedGen fl 5 (MkX 0) (MkX 1) (MkX 0)
  ]
