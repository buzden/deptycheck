module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty String) => (n : Nat) -> Gen MaybeEmpty (X'S n)
checkedGen = deriveGen {core=Ext_X'S}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0 @{smallStrs}
  , G $ \fl => checkedGen fl 18 @{smallStrs}
  ]
