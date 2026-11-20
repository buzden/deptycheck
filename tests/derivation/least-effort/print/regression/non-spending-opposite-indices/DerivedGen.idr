module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Nat -> Type where
  L  : X n m
  C1 : X n (S m) -> X (S n) m
  C2 : X (S n) m -> X n (S m)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n, m : Nat) -> Gen MaybeEmpty (X n m)
