module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : x `LT2` S (S x)
  Step : x `LT2` y -> x `LT2` S y

%runElab printDerived @{LeastEffort} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (a ** b ** LT2 a b)
