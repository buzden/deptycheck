module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

data X = MkX (String, Nat, String)

%runElab derive "X" [Generic, Meta, Show]

export
derivedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen X
--derivedGen = deriveGen
derivedGen _ = empty
