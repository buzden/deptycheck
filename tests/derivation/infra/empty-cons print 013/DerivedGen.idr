module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X n (S n) m n
  XS : X n n m m

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{EmptyCons} $ Fuel -> (n, m, p, k : Nat) -> Gen MaybeEmpty (X n m p k)
