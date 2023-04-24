module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX Void

%runElab derive "X" [Generic, Meta, Show]

voidsGen : Fuel -> Gen CanBeEmptyStatic Void
voidsGen _ = empty

checkedGen : Fuel -> (Fuel -> Gen CanBeEmptyStatic Void) => Gen CanBeEmptyStatic X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{voidsGen} ]
