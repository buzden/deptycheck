module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX String String

%runElab derive "X" [Generic, Meta, Show]

%hint
hintedStringGen : Fuel -> Gen String
hintedStringGen _ = elements ["very-external", "hinted"]

-- shall not use hinted strings gen, shall use the given one
export
checkedGen : Fuel -> (Fuel -> Gen String) => Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]
