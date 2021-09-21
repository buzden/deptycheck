module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

export
checkedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen (String, Nat, String)
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
