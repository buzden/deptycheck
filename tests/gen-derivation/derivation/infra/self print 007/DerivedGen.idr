module DerivedGen

import AlternativeCore

%default total

%language ElabReflection

data X : Nat -> Bool -> Type where
  X0 : X 0 True
  X1 : X 1 False

%runElab printDerived @{CallSelf} $ Fuel -> Gen (n : Nat ** b : Bool ** X n b)
