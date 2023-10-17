module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty Bool
checkedGen = deriveGen {core=EmptyBody}

main : IO Unit
main = runGs [ G checkedGen ]
