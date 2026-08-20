module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect n (Fin m) -> X m

Show (X m) where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> Gen MaybeEmpty (m ** X m)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G checkedGen ]
