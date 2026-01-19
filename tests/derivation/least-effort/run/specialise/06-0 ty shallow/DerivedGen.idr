module DerivedGen

import RunDerivedGen

%default total

data Y : Type -> Type where
  MkY : Either Nat a -> Y a

data X : Type where
  MkX : Either Nat (Y Nat) -> X

Show a => Show (Y a) where
  showPrec d $ MkY e = showCon d "MkY" $ showArg e

Show X where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G checkedGen ]
