module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Bool -> Type where
  X0 : X 0 True
  X1 : X 1 False

%runElab deriveGenPrinter @{CallSelf} $ Fuel -> Gen MaybeEmpty (n : Nat ** b : Bool ** X n b)
