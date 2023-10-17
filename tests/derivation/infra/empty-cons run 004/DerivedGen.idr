module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

Show (X n) where
  show MkX = "MkX"

checkedGen : Fuel -> Gen MaybeEmpty (n ** X n)
checkedGen = deriveGen {core=EmptyCons}

main : IO Unit
main = runGs
  [ G checkedGen
  ]
