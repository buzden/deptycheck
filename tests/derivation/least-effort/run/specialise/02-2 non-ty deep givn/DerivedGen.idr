module DerivedGen

import Data.Fin
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : List (Fin n) -> X n

Show (X n) where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> (n : _) -> Gen MaybeEmpty $ X n
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 1
  , G $ \fl => checkedGen fl 3
  ]
