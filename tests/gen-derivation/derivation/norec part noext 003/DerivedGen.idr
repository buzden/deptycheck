module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX (Maybe Bool)

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> Gen X
--checkedGen = deriveGen
checkedGen _ = empty

main : IO ()
main = runGs [ G checkedGen ]
