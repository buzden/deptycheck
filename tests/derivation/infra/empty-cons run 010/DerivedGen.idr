module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

checkedGen : Fuel -> (n : Nat) -> (a : Type) -> Gen MaybeEmpty (Vect n a)
checkedGen = deriveGen @{EmptyCons}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0 Void
  , G $ \fl => checkedGen fl 9 Void
  , G $ \fl => checkedGen fl 0 Nat
  ]
