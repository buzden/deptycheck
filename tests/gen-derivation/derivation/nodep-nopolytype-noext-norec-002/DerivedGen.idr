module DerivedGen

import public Test.DepTyCheck.Gen.Auto

%default total

%language ElabReflection

export
derivedGen : Fuel -> Gen Bool
--derivedGen = deriveGen
derivedGen = const empty
