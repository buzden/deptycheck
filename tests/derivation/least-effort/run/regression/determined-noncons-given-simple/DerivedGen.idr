module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data A : Nat -> Type where
    A1 : (0 a : Nat) -> (0 b : Nat) -> A (a + b)
    A2 : (0 a : Nat) -> (0 b : Nat) -> A (a + b + 2)

data B : A n -> Type where
    B1 : B $ A1 a b
    B2 : B $ A2 a b

checkedGen : Fuel -> (n : Nat) -> (sub : A n) -> Gen MaybeEmpty (B sub)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (B a) where
  show B1 = "B1"
  show B2 = "B2"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 5 $ A1 2 3
  , G $ \fl => checkedGen fl 7 $ A2 2 3
  ]
