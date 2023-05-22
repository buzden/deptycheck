module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{CallSelf} $ Fuel -> (Fuel -> Gen CanBeEmptyStatic Nat) => Gen CanBeEmptyStatic Bool
