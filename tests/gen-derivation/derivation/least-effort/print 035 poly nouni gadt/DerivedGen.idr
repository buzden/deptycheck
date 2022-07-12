module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

-- no need for universal generator for any of constructors (arguably)
data X : Type -> Type where
  XN : X Nat
  XA : (x : a) -> X a
  XE : X $ List a
  XL : (x : List a) -> X $ List a
  XM : Maybe (List a) -> X $ List a

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> {a : Type} -> (Fuel -> Gen a) => Gen (X a)
