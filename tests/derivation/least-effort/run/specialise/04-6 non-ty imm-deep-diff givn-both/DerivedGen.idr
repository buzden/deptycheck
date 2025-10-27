module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Nat -> Type where
  MkX : Vect n (Fin m) -> X n m

Show (X n m) where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> (n, m : _) -> Gen MaybeEmpty $ X n m
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0 0
  , G $ \fl => checkedGen fl 0 3
  , G $ \fl => checkedGen fl 1 0
  , G $ \fl => checkedGen fl 1 1
  , G $ \fl => checkedGen fl 1 3
  , G $ \fl => checkedGen fl 3 1
  , G $ \fl => checkedGen fl 3 3
  ]
