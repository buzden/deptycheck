module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Fin

%default total

data X : (n : Nat) -> Fin n -> Type where
  MkX : (n : _) -> (f : _) -> X (S (S n)) (FS (FS f))

%language ElabReflection

main : IO Unit
main = %runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> (f : Fin n) -> Gen $ X n f
