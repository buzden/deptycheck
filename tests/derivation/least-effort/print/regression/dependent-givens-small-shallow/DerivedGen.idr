module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Fin

%default total

data X : (n : Nat) -> Fin n -> Type where
  MkX : (n : _) -> (f : _) -> X (S n) (FS f)

%language ElabReflection

%runElab printDerived @{LeastEffort} $ Fuel -> (n : Nat) -> (f : Fin n) -> Gen MaybeEmpty $ X n f
