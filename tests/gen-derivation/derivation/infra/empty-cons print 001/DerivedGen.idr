module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

main : IO Unit
main = %runElab printDerived @{EmptyCons} $ Fuel -> Gen Unit
