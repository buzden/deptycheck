module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect n (Fin m) -> X n m

Show (X n m) where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> Gen MaybeEmpty (n ** m ** X n m)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G checkedGen ]
