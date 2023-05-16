module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN x x

main : IO Unit
main = %runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen (a ** b ** EqualN a b)
