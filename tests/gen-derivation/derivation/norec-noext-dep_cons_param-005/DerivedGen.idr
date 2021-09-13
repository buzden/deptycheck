module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

data X = X0 | X1 (Maybe Bool) | X2 Bool (Bool, Bool)

%runElab derive "X" [Generic, Meta, Show]

export
derivedGen : Fuel -> Gen X
--derivedGen = deriveGen
derivedGen _ = empty
