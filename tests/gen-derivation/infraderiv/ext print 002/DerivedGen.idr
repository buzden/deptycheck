module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

%runElab printDerived @{Ext_XSS} $ Fuel -> (Fuel -> Gen String) => Gen XSS
