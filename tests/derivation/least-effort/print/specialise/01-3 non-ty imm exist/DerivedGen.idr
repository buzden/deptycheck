module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X = MkX (Vect n String)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
