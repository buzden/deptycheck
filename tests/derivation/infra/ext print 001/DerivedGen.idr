module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%runElab deriveGenPrinter @{Ext_XS} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty XS
