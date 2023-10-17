module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

data X : Nat -> Nat -> Nat -> Nat -> Type where
  MkX : X n n n n

%language ElabReflection

%runElab printDerived @{LeastEffort} $ Fuel -> (x1 : Nat) -> (x2 : Nat) -> (x3 : Nat) -> (x4 : Nat) -> Gen MaybeEmpty $ X x1 x2 x3 x4
