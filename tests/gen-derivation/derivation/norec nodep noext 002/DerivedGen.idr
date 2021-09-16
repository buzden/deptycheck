module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = X0 | X1 Bool | X2 Bool Bool

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> Gen X
--checkedGen = deriveGen
checkedGen = const empty

main : IO ()
main = runGs [ G checkedGen ]
