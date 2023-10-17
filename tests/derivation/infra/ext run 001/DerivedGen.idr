module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty XS
checkedGen = deriveGen {core=Ext_XS}

main : IO Unit
main = runGs [ G $ \fl => checkedGen fl @{smallStrs} ]
