module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%language ElabReflection

data X = A | B | C

ProbabilityTuning "A".dataCon where
  isConstructor = itIsConstructor
  tuneWeight = (*2)

ProbabilityTuning "B".dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = 4

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

%hint ShowX : Show X; ShowX = %runElab derive

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
