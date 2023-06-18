module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX Void

%runElab derive "X" [Generic, Meta, Show]

voidsGen : Fuel -> Gen MaybeEmpty Void
voidsGen _ = empty

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty Void) => Gen MaybeEmpty X
checkedGen = deriveGen

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{voidsGen} ]
