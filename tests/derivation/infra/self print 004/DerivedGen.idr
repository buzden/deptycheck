module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

%runElab deriveGenPrinter @{CallSelf} $ Fuel -> (n : Nat) -> Gen MaybeEmpty (X n)
