module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{LeastEffort} $ Fuel -> Gen MaybeEmpty Nat
