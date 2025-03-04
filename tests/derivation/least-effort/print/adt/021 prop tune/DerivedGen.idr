module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X = A | B | C

ProbabilityTuning "A".dataCon where
  isConstructor = itIsConstructor
  tuneWeight = (*2)

ProbabilityTuning "B".dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = 4

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
