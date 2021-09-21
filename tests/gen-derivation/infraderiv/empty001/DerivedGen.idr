module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen Unit
checkedGen = deriveGen @{Empty}

main : IO Unit
main = runGs [ G checkedGen ]
