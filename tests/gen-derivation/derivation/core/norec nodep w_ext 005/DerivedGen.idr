module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX Void

%runElab derive "X" [Generic, Meta, Show]

voidsGen : Fuel -> Gen0 Void
voidsGen _ = empty

checkedGen : Fuel -> (Fuel -> Gen0 Void) => Gen0 X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{voidsGen} ]
