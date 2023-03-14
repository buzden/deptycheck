module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen0 Bool
checkedGen = deriveGen @{EmptyBody}

main : IO Unit
main = runGs [ G checkedGen ]
