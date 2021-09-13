module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

export
checkedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen (String, Nat)
checkedGen = deriveGen
