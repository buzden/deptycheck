module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived @{Ext_XSN} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => (n : Nat) -> Gen MaybeEmpty (X'S n)
