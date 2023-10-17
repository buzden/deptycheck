module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Fin

%default total

%language ElabReflection

%runElab printDerived @{LeastEffort} $ Fuel -> Gen MaybeEmpty (n ** Fin n)
