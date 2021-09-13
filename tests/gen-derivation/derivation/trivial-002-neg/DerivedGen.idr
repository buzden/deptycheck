module DerivedGen

import public Test.DepTyCheck.Gen.Auto

%default total

%language ElabReflection

export
derivedGen : Fuel -> Gen Void
derivedGen = deriveGen
