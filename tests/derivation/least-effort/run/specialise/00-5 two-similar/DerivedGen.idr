module DerivedGen

import RunDerivedGen

%default total

data X = MkX (List String) (List Nat)

Show X where
  showPrec d $ MkX xs ys = showCon d "MkX" $ showArg xs ++ showArg ys

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{const $ elements ["a", "b", "c", "cc"]} ]
