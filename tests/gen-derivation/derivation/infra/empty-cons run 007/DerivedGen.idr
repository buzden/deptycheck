module DerivedGen

import AlternativeCore
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

checkedGen : Fuel -> Gen CanBeEmptyStatic (n ** a ** Vect n a)
checkedGen = deriveGen @{EmptyCons}

Show (n ** a ** Vect n a) where
  show _ = "Vect ..."

main : IO Unit
main = runGs
  [ G checkedGen
  ]
