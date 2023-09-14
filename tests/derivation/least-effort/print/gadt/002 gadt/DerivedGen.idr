module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Fin

%default total

%language ElabReflection

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (n ** Fin n)
