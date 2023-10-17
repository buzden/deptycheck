module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty XSS
checkedGen = deriveGen {core=Ext_XSS}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]
