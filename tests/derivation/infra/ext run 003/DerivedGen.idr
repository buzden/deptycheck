module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty XSN
checkedGen = deriveGen {core=Ext_XSN}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
