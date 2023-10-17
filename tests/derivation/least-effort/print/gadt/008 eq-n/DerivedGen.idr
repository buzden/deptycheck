module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN x x

%runElab printDerived @{LeastEffort} $ Fuel -> (a : Nat) -> Gen MaybeEmpty (b ** EqualN a b)
