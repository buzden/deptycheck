module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Fin

%default total

%language ElabReflection

%runElab printDerived @{LeastEffort} $ Fuel -> (n : Nat) -> Gen MaybeEmpty $ Fin n
