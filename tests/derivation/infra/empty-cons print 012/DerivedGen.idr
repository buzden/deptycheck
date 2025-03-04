module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Nat -> Type where
  XE : X n n
  XS : X n (S n)

%runElab deriveGenPrinter @{EmptyCons} $ Fuel -> (n, m : Nat) -> Gen MaybeEmpty (X n m)
