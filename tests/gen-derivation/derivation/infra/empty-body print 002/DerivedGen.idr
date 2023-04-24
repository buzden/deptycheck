module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{EmptyBody} $ Fuel -> (n : Nat) -> (a : Type) -> Gen CanBeEmptyStatic (Vect n a)
