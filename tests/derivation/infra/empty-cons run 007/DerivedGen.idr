module DerivedGen

import AlternativeCore
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

checkedGen : Fuel -> Gen MaybeEmpty (n ** a ** Vect n a)
checkedGen = deriveGen {core=EmptyCons}

Show (n ** a ** Vect n a) where
  show _ = "Vect ..."

main : IO Unit
main = runGs
  [ G checkedGen
  ]
