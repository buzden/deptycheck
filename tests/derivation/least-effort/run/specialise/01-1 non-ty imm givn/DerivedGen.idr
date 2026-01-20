module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect n String -> X n

Show (X n) where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => (n : _) -> Gen MaybeEmpty $ X n
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen @{smallStrs} fl 0
  , G $ \fl => checkedGen @{smallStrs} fl 1
  , G $ \fl => checkedGen @{smallStrs} fl 3
  ]
