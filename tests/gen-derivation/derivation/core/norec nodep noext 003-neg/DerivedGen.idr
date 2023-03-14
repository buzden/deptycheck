module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX Void

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> Gen0 X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]
