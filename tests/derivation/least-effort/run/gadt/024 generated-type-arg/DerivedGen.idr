module DerivedGen

import RunDerivedGen

%default total

data X : Type -> Type where
  Z : X Nat
  Y : X t -> X $ List t

checkedGen : Fuel -> Gen MaybeEmpty (t ** X t)
checkedGen = deriveGen

[Ty] Show (X t) where
  showPrec d Z = "Nat"
  showPrec d (Y x) = showCon d "List" $ showArg x

Show (t ** X t) where
  show (_ ** x) = "_ : X $ \{show @{Ty} x}"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
