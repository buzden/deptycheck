module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X = MkX (List Nat)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
