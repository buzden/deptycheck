module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

export
checkedGen : Fuel -> (Fuel -> Gen CanBeEmptyStatic String) => (Fuel -> Gen CanBeEmptyStatic Nat) => Gen CanBeEmptyStatic (String, Nat)
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
