module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty (n ** a ** Vect n a)
checkedGen = deriveGen @{EmptyBody}

Show (n ** a ** Vect n a) where
  show _ = "Vect ..."

main : IO Unit
main = runGs
  [ G checkedGen
  ]
