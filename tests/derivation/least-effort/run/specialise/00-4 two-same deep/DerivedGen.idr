module DerivedGen

import RunDerivedGen

%default total

data Y = MkY (List Nat)

data X = MkX (List Nat) Y

Show Y where
  showPrec d $ MkY xs = showCon d "MkY" $ showArg xs

Show X where
  showPrec d $ MkX xs y = showCon d "MkX" $ showArg xs ++ showArg y

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO Unit
main = runGs [ G checkedGen ]
