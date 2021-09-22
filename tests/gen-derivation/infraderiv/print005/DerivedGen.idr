module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

covering
main : IO Unit
main = printDerived @{Empty} $ Fuel -> Gen (n : Nat ** X n)
