module DerivedGen

import RunDerivedGen

%default total

X : Type
X = Bool

checkedGen : Fuel -> Gen0 X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G checkedGen
  ]
