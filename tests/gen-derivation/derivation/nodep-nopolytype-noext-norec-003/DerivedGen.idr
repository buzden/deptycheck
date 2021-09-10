module DerivedGen

import public Test.DepTyCheck.Gen.Auto

import Generics.Derive

%default total

%language ElabReflection

public export
data X = X0 | X1 Bool | X2 Bool Bool

%runElab derive "X" [Generic, Meta, Show]

export
derivedGen : Fuel -> Gen X
--derivedGen = deriveGen
derivedGen = const empty
