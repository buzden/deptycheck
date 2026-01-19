module DerivedGen

import RunDerivedGen

%default total

data Z : Type -> Type where
  MkZ : Either Nat a -> Z a

data Y : Type -> Type where
  MkY : Either (Z a) a -> Y a

data X : Type where
  MkX : Y Nat -> X

Show a => Show (Z a) where
  showPrec d $ MkZ e = showCon d "MkZ" $ showArg e

Show a => Show (Y a) where
  showPrec d $ MkY e = showCon d "MkY" $ showArg e

Show X where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G checkedGen ]
