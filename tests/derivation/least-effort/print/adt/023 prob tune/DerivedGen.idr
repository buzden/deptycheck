module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X = A X | B | C | D

ProbabilityTuning "B".dataCon where
  isConstructor = itIsConstructor
  tuneWeight = (*2)

ProbabilityTuning "C".dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = 4

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty X
