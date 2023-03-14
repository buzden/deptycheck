module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

export
checkedGen : Fuel -> (Fuel -> Gen0 String) => (Fuel -> Gen0 Nat) => Gen0 (String, Nat, String)
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
