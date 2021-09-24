module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX Bool Void

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> Gen X
--checkedGen = deriveGen
checkedGen = const empty

main : IO ()
main = runGs [ G checkedGen ]
