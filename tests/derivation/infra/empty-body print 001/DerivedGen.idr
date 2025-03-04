module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%runElab deriveGenPrinter @{EmptyBody} $ Fuel -> Gen MaybeEmpty Unit
