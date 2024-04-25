module DerivedGen

import RunDerivedGen

%default total

X : Type
X = Bool

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G checkedGen
  ]
