module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{Ext_XSN} $ Fuel -> (Fuel -> Gen0 String) => (Fuel -> Gen0 Nat) => Gen0 XSN
