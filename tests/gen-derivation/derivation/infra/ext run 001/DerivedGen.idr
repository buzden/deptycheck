module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen0 String) => Gen0 XS
checkedGen = deriveGen @{Ext_XS}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]
