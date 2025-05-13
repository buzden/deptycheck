module DerivedGen

import RunDerivedGen

%default total

data Y : Bool -> Nat -> Type where
  MkY : Y l n

data X : (b : _) -> Y (not b) n -> Type where
  MkX : X b MkY

checkedGen : Fuel -> (b : _) -> (n : _) -> (y : Y (not b) n) -> Gen0 $ X b y
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (X b y) where
  show MkX = "MkX"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl True Z MkY
  ]
