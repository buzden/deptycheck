module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

data X = MkX String String

%runElab derive "X" [Generic, Meta, Show]

export
checkedGen : Fuel -> (Fuel -> Gen String) => Gen X
--checkedGen = deriveGen
checkedGen _ = empty
