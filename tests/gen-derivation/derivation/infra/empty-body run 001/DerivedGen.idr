module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty Unit
checkedGen = deriveGen @{EmptyBody}

main : IO Unit
main = runGs [ G checkedGen ]
