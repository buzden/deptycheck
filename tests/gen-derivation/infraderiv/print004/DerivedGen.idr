module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

%runElab printDerived @{Empty} $ Fuel -> (n : Nat) -> Gen (X n)
