module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{Ext_XSN} $ Fuel -> (Fuel -> Gen CanBeEmptyStatic String) => (n : Nat) -> Gen CanBeEmptyStatic (X'S n)
