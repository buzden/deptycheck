module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

data IsFS : (n : _) -> Fin n -> Type where
  ItIsFS : IsFS _ (FS i)

checkedGen : Fuel -> {n : Nat} -> (v : Fin n) -> Gen MaybeEmpty $ IsFS n v
checkedGen = deriveGen @{EmptyCons}

Show (IsFS n a) where
  show ItIsFS = "ItisFS"

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl {n=3} 2
  , G $ \fl => checkedGen fl {n=3} 0
  ]
