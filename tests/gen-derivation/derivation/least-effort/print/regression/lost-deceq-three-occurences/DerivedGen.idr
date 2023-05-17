module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

data X : Nat -> Nat -> Nat -> Type where
  MkX : X n n n

%language ElabReflection

main : IO Unit
main = %runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (x1 : Nat) -> (x2 : Nat) -> (x3 : Nat) -> Gen $ X x1 x2 x3
