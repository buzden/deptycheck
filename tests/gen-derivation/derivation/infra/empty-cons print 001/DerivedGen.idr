module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{EmptyCons} $ Fuel -> Gen CanBeEmptyStatic Unit
