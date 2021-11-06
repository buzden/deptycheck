module DerivedGen

import RunDerivedGen

import Test.DepTyCheck.Gen.Auto.Core.ObligatoryExternals

%default total

%language ElabReflection

checkedGen : Fuel -> Gen Void
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]
