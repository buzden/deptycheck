module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{EmptyBody} $ Fuel -> Gen0 Unit
