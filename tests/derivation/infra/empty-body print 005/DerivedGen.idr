module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : X n

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{EmptyBody} $ Fuel -> Gen MaybeEmpty (n : Nat ** X n)
