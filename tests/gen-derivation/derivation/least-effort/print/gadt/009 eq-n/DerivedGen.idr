module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN x x

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (b : Nat) -> Gen CanBeEmptyStatic (a ** EqualN a b)
