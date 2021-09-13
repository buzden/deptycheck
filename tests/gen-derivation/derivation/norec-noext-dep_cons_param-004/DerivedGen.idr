module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

data X = MkX (Bool, Bool)

%runElab derive "X" [Generic, Meta, Show]

export
derivedGen : Fuel -> Gen X
--derivedGen = deriveGen
derivedGen _ = empty
