module DerivedGen

import RunDerivedGen

%default total

data Y : Type -> Type where
  MkY : Either Nat a -> Y a

data X : Type where
  MkX : Either Nat (Y $ Either (Fin 5) String) -> X

Show a => Show (Y a) where
  showPrec d $ MkY e = showCon d "MkY" $ showArg e

Show X where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G $ \fl => checkedGen @{smallStrs} fl ]
