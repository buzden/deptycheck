module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

%runElab printDerived @{CallSelf} $ Fuel -> Gen (n : Nat ** X n)
