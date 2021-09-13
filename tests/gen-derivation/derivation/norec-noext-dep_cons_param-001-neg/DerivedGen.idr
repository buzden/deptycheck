module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

export
checkedGen : Fuel -> Gen (Maybe Bool)
checkedGen = deriveGen
