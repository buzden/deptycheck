module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{EmptyCons} $ Fuel -> Gen CanBeEmptyStatic (n : Nat ** a : Type ** Vect n a)
