module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{CallSelf} $ Fuel -> (a : Type) -> Gen MaybeEmpty (n : Nat ** Vect n a)
