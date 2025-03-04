module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

X : Type
X = Bool

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
