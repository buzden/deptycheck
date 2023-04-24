module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{EmptyCons} $ Fuel -> (Fuel -> Gen CanBeEmptyStatic Nat) => Gen CanBeEmptyStatic Bool
