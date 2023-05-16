module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Fin

%default total

%language ElabReflection

main : IO Unit
main = %runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen (n ** Fin n)
