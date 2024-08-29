module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen
import RunDerivedGen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

Show (X n) where
  show MkX = "MkX"

checkedGen : Fuel -> Gen MaybeEmpty (n ** X n)
checkedGen = deriveGen @{EmptyCons}

main : IO Unit
main = runGs
  [ G checkedGen
  ]
