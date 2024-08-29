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

checkedGen : Fuel -> (n : Nat) -> Gen MaybeEmpty (X n)
checkedGen = deriveGen @{CallSelf}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 18
  ]
