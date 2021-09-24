module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen XSN
checkedGen = deriveGen @{Ext_XSN}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} @{smallNats} ]
