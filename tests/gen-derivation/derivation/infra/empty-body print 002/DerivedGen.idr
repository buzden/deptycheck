module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

main : IO Unit
main = %runElab printDerived @{EmptyBody} $ Fuel -> (n : Nat) -> (a : Type) -> Gen (Vect n a)
