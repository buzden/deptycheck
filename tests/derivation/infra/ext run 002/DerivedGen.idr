module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty XSS
checkedGen = deriveGen @{Ext_XSS}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]
