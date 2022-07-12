module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

-- no need for universal generator for any of constructors (arguably)
data X : (l, r : Type) -> Type where
  XNN : X Nat Nat
  XAB : (x : a) -> (x : b) -> X a b
  XE' : X (List a) (List a)
  XL  : (x : List a) -> (y : List b) -> X (List a) (List b)
  XL' : (x : List a) -> (y : List a) -> X (List a) (List a) -- both gen of `l` and of `r` can be used for the argument
  XM  : Maybe (List a) -> X (List a) (List b)
  XM' : Maybe (List a) -> X (List a) (List a) -- both gen of `l` and of `r` can be used for the argument

%runElab printDerived @{MainCoreDerivator @{LeastEffort}} $ Fuel -> {a : Type} -> (Fuel -> Gen a) => {b : Type} -> (Fuel -> Gen b) => Gen (X a b)
