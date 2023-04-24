module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen CanBeEmptyStatic Bool
checkedGen = deriveGen @{EmptyCons}

main : IO Unit
main = runGs [ G checkedGen ]
