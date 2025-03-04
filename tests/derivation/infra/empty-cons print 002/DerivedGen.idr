module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%language ElabReflection

%runElab deriveGenPrinter @{EmptyCons} $ Fuel -> (n : Nat) -> (a : Type) -> Gen MaybeEmpty (Vect n a)
