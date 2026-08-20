module DerivedGen

import RunDerivedGen

%default total

data Z : Type -> Type where
  MkZ : Either Nat a -> Z a

data Y : (Type -> Type) -> Type -> Type where
  MkY : Either (f a) a -> Y f a

data X : Type where
  MkX : Y Z Nat -> X

Show a => Show (Z a) where
  showPrec d $ MkZ e = showCon d "MkZ" $ showArg e

Show (f a) => Show a => Show (Y f a) where
  showPrec d $ MkY e = showCon d "MkY" $ showArg e

Show X where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G checkedGen ]
