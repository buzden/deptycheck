module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{Ext_XS} $ Fuel -> (Fuel -> Gen CanBeEmptyStatic String) => Gen CanBeEmptyStatic XS
