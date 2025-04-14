module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data A : Nat -> Type where
    A1 : (0 a : Nat) -> (0 b : Nat) -> A (a + b)
    A2 : (0 a : Nat) -> (0 b : Nat) -> A (a + b + 2)

data B : A n -> Type where
    B1 : B $ A1 a b
    B2 : B $ A2 a b

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> (sub : A n) -> Gen MaybeEmpty (B sub)
