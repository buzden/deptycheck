module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

data X = X1 String Nat | X2 Nat | X3 String

%runElab derive "X" [Generic, Meta, Show]

export
derivedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen X
--derivedGen = deriveGen
derivedGen _ = empty
