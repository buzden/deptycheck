module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{EmptyCons} $ Fuel -> (a : Type) -> Gen CanBeEmptyStatic (n : Nat ** Vect n a)
