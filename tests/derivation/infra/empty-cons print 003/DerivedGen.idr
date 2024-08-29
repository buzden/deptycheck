module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{EmptyCons} $ Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty Bool
