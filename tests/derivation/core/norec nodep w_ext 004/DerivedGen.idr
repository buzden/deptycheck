module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = X1 String Nat | X2 Nat | X3 String

%hint
XShow : Show X
XShow = %runElab derive

export
checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
