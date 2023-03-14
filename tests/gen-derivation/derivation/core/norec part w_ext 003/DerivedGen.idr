module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX (String, Nat, String)

%runElab derive "X" [Generic, Meta, Show]

export
checkedGen : Fuel -> (Fuel -> Gen0 String) => (Fuel -> Gen0 Nat) => Gen0 X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
