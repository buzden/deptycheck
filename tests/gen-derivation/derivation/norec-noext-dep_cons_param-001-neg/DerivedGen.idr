module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

export
derivedGen : Fuel -> Gen (Maybe Bool)
derivedGen = deriveGen
