module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X : Type where
  E : X
  R : X -> Nat -> X

%hint
XShow : Show X
XShow = %runElab derive

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs [ G $ \fl => checkedGen fl ]
