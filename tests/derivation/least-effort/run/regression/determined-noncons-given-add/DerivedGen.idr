module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data A : Nat -> Nat -> Type where
    A1 : (0 a : Nat) -> (0 b : Nat) -> A (S x) (a + b)
    A2 : (0 a : Nat) -> (0 b : Nat) -> A (S x) (a + b + 2)

data B : A x n -> Type where
    B1 : B $ A1 a b
    B2 : B $ A2 a b

checkedGen : Fuel -> (n : Nat) -> (x : Nat) -> (sub : A x n) -> Gen MaybeEmpty (B sub)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (B a) where
  show B1 = "B1"
  show B2 = "B2"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 5 8 $ A1 2 3
  , G $ \fl => checkedGen fl 7 3 $ A2 2 3
  ]
