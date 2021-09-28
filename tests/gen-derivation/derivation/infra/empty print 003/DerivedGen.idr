module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Vect

%default total

%language ElabReflection

%runElab printDerived @{Empty} $ Fuel -> (Fuel -> Gen Nat) => Gen Bool
