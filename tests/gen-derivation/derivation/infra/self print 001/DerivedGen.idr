module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{CallSelf} $ Fuel -> Gen CanBeEmptyStatic Unit
