module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data A : Nat -> Nat -> Type where
    A1 : (0 a : Nat) -> (0 b : Nat) -> A (S x) (a + b)
    A2 : (0 a : Nat) -> (0 b : Nat) -> A (S x) (a + b + 2)

data B : A x n -> Type where
    B1 : B $ A1 a b
    B2 : B $ A2 a b

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> (x : Nat) -> (sub : A x n) -> Gen MaybeEmpty (B sub)
