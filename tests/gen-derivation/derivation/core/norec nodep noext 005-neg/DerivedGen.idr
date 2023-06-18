module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = X0 | X1 Bool | X2 Void Bool

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]
