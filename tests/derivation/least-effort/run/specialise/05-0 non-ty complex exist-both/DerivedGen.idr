module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Type where
  MkX : Vect n (Fin n) -> Either (n `LT` m) (m `LT` n) => X

Show X where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G checkedGen ]
