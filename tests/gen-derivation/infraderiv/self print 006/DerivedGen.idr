module DerivedGen

import AlternativeCore

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{CallSelf} $ Fuel -> (a : Type) -> Gen (n : Nat ** Vect n a)
