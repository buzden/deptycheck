module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X = MkX (List String) (List $ Fin n)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
