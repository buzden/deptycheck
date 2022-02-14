module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{Ext_XSN} $ Fuel -> (Fuel -> Gen String) => (n : Nat) -> Gen (X'S n)
