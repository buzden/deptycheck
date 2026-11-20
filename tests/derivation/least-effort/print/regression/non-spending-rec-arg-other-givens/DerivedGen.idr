module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Nat -> Type where
  L : X n m
  N : X n k -> X (S n) m

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n, m : Nat) -> Gen MaybeEmpty (X n m)
