module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX (String, Nat)

%runElab derive "X" [Generic, Meta, Show]

export
checkedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => (Fuel -> (a, b : Type) -> (Fuel -> Gen a) => (Fuel -> Gen b) => Gen (a, b)) => Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} @{aPair} ]
