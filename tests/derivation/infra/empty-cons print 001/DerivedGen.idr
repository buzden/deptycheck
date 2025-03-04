module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%runElab deriveGenPrinter @{EmptyCons} $ Fuel -> Gen MaybeEmpty Unit
