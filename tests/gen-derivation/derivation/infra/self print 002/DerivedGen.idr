module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{CallSelf} $ Fuel -> (n : Nat) -> (a : Type) -> Gen0 (Vect n a)
