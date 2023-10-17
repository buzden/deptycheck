module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : Nat -> Nat -> Nat -> Nat -> Type where
  XE : X n (S n) m n
  XS : X n n m m

%runElab printDerived {core=EmptyCons} $ Fuel -> (n, m, p, k : Nat) -> Gen MaybeEmpty (X n m p k)
