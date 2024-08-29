module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty Bool
checkedGen = deriveGen @{EmptyBody}

main : IO Unit
main = runGs [ G checkedGen ]
