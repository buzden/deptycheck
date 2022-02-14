module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data X = X0 | X1 (Maybe Bool) | X2 Bool (Bool, Bool)

%runElab derive "X" [Generic, Meta, Show]

export
checkedGen : Fuel -> Gen X
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]
