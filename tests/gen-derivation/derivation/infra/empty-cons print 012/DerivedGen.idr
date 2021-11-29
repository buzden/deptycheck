module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : Nat -> Nat -> Type where
  XE : X n n
  XS : X n (S n)

%runElab printDerived @{EmptyCons} $ Fuel -> (n, m : Nat) -> Gen (X n m)
