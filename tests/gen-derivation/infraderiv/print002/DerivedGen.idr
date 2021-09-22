module DerivedGen

import AlternativeCore

import Data.Vect

%default total

%language ElabReflection

covering
main : IO Unit
main = printDerived @{Empty} $ Fuel -> (n : Nat) -> (a : Type) -> Gen (Vect n a)
