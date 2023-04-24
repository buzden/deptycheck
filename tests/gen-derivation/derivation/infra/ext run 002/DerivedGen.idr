module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen CanBeEmptyStatic String) => Gen CanBeEmptyStatic XSS
checkedGen = deriveGen @{Ext_XSS}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]
