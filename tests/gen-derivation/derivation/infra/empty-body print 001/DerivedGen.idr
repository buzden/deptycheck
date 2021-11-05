module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{EmptyBody} $ Fuel -> Gen Unit
