module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

checkedGen : Fuel -> (a : Type) -> Gen MaybeEmpty (n ** Vect n a)
checkedGen = deriveGen @{EmptyCons}

Show (a ** Vect n a) where
  show _ = "Vect ..."

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl Void
  , G $ \fl => checkedGen fl Nat
  ]
