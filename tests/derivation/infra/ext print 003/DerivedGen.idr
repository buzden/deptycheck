module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%runElab deriveGenPrinter @{Ext_XSN} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty XSN
