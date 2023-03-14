module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen0 Bool
checkedGen = deriveGen @{CallSelf}

main : IO Unit
main = runGs [ G checkedGen ]
