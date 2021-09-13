module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

export
derivedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen (String, Nat, String)
derivedGen = deriveGen
