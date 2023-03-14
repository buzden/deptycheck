module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{Ext_XSS} $ Fuel -> (Fuel -> Gen0 String) => Gen0 XSS
