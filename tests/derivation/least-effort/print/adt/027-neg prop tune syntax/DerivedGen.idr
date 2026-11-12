module DerivedGen


import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection


data X = A | B Nat | C

%runElab tuneProbability "A".dataCon (*2)
%runElab tuneProbability `{CC} (const 4)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
