module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X = MkX (List String) (List $ Fin n)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
