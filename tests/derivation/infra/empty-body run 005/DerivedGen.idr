module DerivedGen

import AlternativeCore
import RunDerivedGen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

Show (X n) where
  show MkX = "MkX"

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (n ** X n)
checkedGen = deriveGen {core=EmptyBody}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl @{smallNats}
  ]
