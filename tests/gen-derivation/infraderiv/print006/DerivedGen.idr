module DerivedGen

import AlternativeCore

import Data.Vect

%default total

%language ElabReflection

covering
main : IO Unit
main = printDerived @{Empty} $ Fuel -> (a : Type) -> Gen (n : Nat ** Vect n a)
