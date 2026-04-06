module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect n (Fin m) -> X n m

Show (X n m) where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> (m : _) -> Gen MaybeEmpty (n ** X n m)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 1
  , G $ \fl => checkedGen fl 3
  ]
