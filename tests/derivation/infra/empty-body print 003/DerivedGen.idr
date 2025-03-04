module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%language ElabReflection

%runElab deriveGenPrinter @{EmptyBody} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty Bool
