module DerivedGen

import AlternativeCore

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{CallSelf} $ Fuel -> Gen (n : Nat ** a : Type ** Vect n a)
