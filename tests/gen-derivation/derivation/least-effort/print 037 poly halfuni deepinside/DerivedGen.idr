module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : (ty : Type) -> Type where
  MkX : Maybe (a, a) -> X $ List a

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> {a : Type} -> (Fuel -> (ty : Type) -> Gen ty) => Gen (X a)
