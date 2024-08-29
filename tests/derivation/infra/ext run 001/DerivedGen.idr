module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty XS
checkedGen = deriveGen @{Ext_XS}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]
