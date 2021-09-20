module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = X1 String Nat | X2 Nat | X3 String

%runElab derive "X" [Generic, Meta, Show]

export
checkedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen X
--checkedGen = deriveGen
checkedGen _ = empty

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
