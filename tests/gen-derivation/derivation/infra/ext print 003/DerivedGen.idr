module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

main : IO Unit
main = %runElab printDerived @{Ext_XSN} $ Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen XSN
