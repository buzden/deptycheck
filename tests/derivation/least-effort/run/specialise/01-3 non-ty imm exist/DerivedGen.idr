module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X = MkX (Vect n String)

Show X where
  showPrec d $ MkX xs = showCon d "MkX" $ showArg xs

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]
