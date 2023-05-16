module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

main : IO Unit
main = %runElab printDerived @{EmptyCons} $ Fuel -> (a : Type) -> Gen (n : Nat ** Vect n a)
