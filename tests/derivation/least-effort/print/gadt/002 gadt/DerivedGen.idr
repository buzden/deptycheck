module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty (n ** Fin n)
