module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

checkedGen : Fuel -> (n : Nat) -> Gen MaybeEmpty (a ** Vect n a)
checkedGen = deriveGen @{EmptyCons}

Show (a ** Vect n a) where
  show _ = "Vect ..."

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 5
  ]
