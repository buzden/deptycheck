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
  show XE = "XE : X \{show n} \{show m} \{show p} \{show k}"
  show XS = "XS : X \{show n} \{show m} \{show p} \{show k}"

checkedGen : Fuel -> (n, m, p, k : Nat) -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (X n m p k)
checkedGen = deriveGen {core=EmptyCons}

main : IO Unit
main = runGs
  [ G $ \fl => checkedGen fl 0 0 0 0 @{smallStrs}
  , G $ \fl => checkedGen fl 1 1 1 1 @{smallStrs}
  , G $ \fl => checkedGen fl 1 2 3 1 @{smallStrs}
  ]
