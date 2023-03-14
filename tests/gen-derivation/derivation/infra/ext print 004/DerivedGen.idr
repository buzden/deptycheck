module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{Ext_XSN} $ Fuel -> (Fuel -> Gen0 String) => (n : Nat) -> Gen0 (X'S n)
