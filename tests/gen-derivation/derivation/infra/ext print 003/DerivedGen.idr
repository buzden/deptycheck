module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

%runElab printDerived @{Ext_XSN} $ Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen XSN
