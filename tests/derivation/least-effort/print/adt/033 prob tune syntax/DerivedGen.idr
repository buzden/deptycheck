module DerivedGen


import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection


data X = A | B | C

%runElab tuneProbabilities
  A (*2)
  B (const 4)

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
