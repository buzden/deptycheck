module DerivedGen

import public Test.DepTyCheck.Gen.Auto

%default total

%language ElabReflection

export
checkedGen : Fuel -> Gen Bool
--checkedGen = deriveGen
checkedGen = const empty
