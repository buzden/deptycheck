module DerivedGen

import AlternativeCore
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

checkedGen : Fuel -> (n : Nat) -> (a : Type) -> Gen0 (Vect n a)
checkedGen = deriveGen @{EmptyBody}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0 Void
  , G $ \fl => checkedGen fl 9 Void
  , G $ \fl => checkedGen fl 0 Nat
  ]
