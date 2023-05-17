module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : x `LT2` S (S x)
  Step : x `LT2` y -> x `LT2` S y

main : IO Unit
main = %runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (b : Nat) -> Gen (a ** LT2 a b)
