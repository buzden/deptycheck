module DerivedGen

import AlternativeCore
import RunDerivedGen

import Data.Vect

%default total

%language ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X n (S n) m n
  XS : X n n m m

{n, m, p, k : Nat} -> Show (X n m p k) where
  show XE = "XE \{show n} \{show m} \{show p} \{show k}"
  show XS = "XS \{show n} \{show m} \{show p} \{show k}"

checkedGen : Fuel -> (n, m, p, k : Nat) -> Gen MaybeEmpty (X n m p k)
checkedGen = deriveGen {core=EmptyCons}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0 0 0 0
  , G $ \fl => checkedGen fl 8 9 7 7
  , G $ \fl => checkedGen fl 5 6 7 8
  ]
