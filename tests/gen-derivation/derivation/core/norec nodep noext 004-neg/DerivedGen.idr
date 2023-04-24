module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = MkX Bool Void

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> Gen CanBeEmptyStatic X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]
