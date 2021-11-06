module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX String

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> (Fuel -> Gen String) => Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]
