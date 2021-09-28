module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX (Bool, Bool)

%runElab derive "X" [Generic, Meta, Show]

export
checkedGen : Fuel -> Gen X
--checkedGen = deriveGen
checkedGen _ = empty

main : IO ()
main = runGs [ G checkedGen ]
