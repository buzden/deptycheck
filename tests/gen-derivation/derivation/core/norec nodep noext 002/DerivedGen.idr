module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = X0 | X1 Bool | X2 Bool Bool

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> Gen0 X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]
