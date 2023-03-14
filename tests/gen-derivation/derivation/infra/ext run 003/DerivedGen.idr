module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen0 String) => (Fuel -> Gen0 Nat) => Gen0 XSN
checkedGen = deriveGen @{Ext_XSN}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
