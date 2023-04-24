module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX String Nat

%runElab derive "X" [Generic, Meta, Show]

export
checkedGen : Fuel -> (Fuel -> Gen CanBeEmptyStatic String) => (Fuel -> Gen CanBeEmptyStatic Nat) => Gen CanBeEmptyStatic X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
