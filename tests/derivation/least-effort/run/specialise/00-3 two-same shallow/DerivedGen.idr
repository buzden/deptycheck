module DerivedGen

import RunDerivedGen

%default total

data X = MkX (List Nat) (List Nat)

Show X where
  showPrec d $ MkX xs ys = showCon d "MkX" $ showArg xs ++ showArg ys

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G checkedGen ]
