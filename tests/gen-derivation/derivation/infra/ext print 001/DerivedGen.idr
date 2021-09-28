module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

%runElab printDerived @{Ext_XS} $ Fuel -> (Fuel -> Gen String) => Gen XS
