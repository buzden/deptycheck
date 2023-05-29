module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX String String

%runElab derive "X" [Generic, Meta, Show]

%hint
hintedStringGen : Fuel -> Gen String
hintedStringGen _ = elements ["very-external", "hinted"]

-- shall use the hinted strings gen
export
checkedGen : Fuel -> Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl ]
