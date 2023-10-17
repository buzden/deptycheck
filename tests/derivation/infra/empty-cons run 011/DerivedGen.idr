module DerivedGen

import AlternativeCore
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

data X : Nat -> Nat -> Type where
  XE : X n n
  XS : X n (S n)

{n, m : Nat} -> Show (X n m) where
  show XE = "XE \{show n} \{show m}"
  show XS = "XS \{show n} \{show m}"

checkedGen : Fuel -> (n, m : Nat) -> Gen MaybeEmpty (X n m)
checkedGen = deriveGen {core=EmptyCons}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0 0
  , G $ \fl => checkedGen fl 9 9
  , G $ \fl => checkedGen fl 5 6
  ]
