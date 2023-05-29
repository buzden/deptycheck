module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX (SomeTestType 2) (SomeTestType 3)

%runElab derive "X" [Generic, Meta, Show]

-- shall not use hinted strings gen, shall use the given one
export
checkedGen : Fuel -> (Fuel -> (n : Nat) -> Gen $ SomeTestType n) => Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{TunableSomeTestTypeGen "given"} ]
