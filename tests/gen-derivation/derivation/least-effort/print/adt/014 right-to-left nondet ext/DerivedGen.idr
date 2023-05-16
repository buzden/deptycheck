module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : String -> Nat -> Type where
  MkX : (n : _) -> (m : _) -> X n m

data Y : Type where
  MkY : X n m -> X n k -> Y

main : IO Unit
main = %runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen String) => (Fuel -> Gen Nat) => Gen Y
