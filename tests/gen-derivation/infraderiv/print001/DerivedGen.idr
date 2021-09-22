module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

covering
main : IO Unit
main = printDerived @{Empty} $ Fuel -> Gen Unit
