module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : x `LT2` S (S x)
  Step : x `LT2` y -> x `LT2` S y

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (b : Nat) -> Gen0 (a ** LT2 a b)
