module DerivedGen

import public RunDerivedGen

%default total

%language ElabReflection

data X = MkX Void

%runElab derive "X" [Generic, Meta, Show]

voidsGen : Fuel -> Gen Void
voidsGen _ = empty

checkedGen : Fuel -> (Fuel -> Gen Void) => Gen X
--checkedGen = deriveGen
checkedGen _ = empty

main : IO ()
main = runGs [ G $ \fl => checkedGen fl @{voidsGen} ]
