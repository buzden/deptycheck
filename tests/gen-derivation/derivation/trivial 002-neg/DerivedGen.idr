module DerivedGen

import public Test.DepTyCheck.Gen.Auto

%default total

%language ElabReflection

export
checkedGen : Fuel -> Gen Void
checkedGen = deriveGen
