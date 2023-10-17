module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty Unit
checkedGen = deriveGen {core=EmptyBody}

main : IO Unit
main = runGs [ G checkedGen ]
