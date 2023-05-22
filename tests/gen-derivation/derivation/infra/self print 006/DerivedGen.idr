module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{CallSelf} $ Fuel -> (a : Type) -> Gen MaybeEmpty (n : Nat ** Vect n a)
