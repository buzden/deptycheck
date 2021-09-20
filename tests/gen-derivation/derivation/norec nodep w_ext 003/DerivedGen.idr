module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX String Nat

%runElab derive "X" [Generic, Meta, Show]

export
checkedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen X
--checkedGen = deriveGen
checkedGen _ = empty

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
