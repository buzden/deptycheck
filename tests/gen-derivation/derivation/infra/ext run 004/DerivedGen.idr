module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> (Fuel -> Gen CanBeEmptyStatic String) => (n : Nat) -> Gen CanBeEmptyStatic (X'S n)
checkedGen = deriveGen @{Ext_X'S}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0 @{smallStrs}
  , G $ \fl => checkedGen fl 18 @{smallStrs}
  ]
