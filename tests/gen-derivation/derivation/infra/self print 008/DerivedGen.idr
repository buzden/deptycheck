module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{CallSelf} $ Fuel -> Gen CanBeEmptyStatic (n : Nat ** a : Type ** Vect n a)
