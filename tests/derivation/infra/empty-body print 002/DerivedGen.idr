module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived {core=EmptyBody} $ Fuel -> (n : Nat) -> (a : Type) -> Gen MaybeEmpty (Vect n a)
