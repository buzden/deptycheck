module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

export
derivedGen : Fuel -> Gen (Bool, Bool)
derivedGen = deriveGen
