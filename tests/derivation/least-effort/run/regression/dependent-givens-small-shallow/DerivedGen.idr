module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : (n : Nat) -> Fin n -> Type where
  MkX : (n : _) -> (f : _) -> X (S n) (FS f)

Show (X n f) where
  show $ MkX n f = "MkX \{show n} \{show f}"

%language ElabReflection

checkedGen : Fuel -> (n : Nat) -> (f : Fin n) -> Gen MaybeEmpty $ X n f
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 3 0
  , G $ \fl => checkedGen fl 2 1
  ]
