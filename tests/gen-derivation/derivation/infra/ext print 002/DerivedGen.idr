module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

main : IO Unit
main = %runElab printDerived @{Ext_XSS} $ Fuel -> (Fuel -> Gen String) => Gen XSS
