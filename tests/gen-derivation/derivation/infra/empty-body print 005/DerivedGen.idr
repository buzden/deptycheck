module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

main : IO Unit
main = %runElab printDerived @{EmptyBody} $ Fuel -> Gen (n : Nat ** X n)
