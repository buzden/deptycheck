module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%language ElabReflection

data X = A | B | C

%runElab tuneProbabilities
  A (*2)
  B (const 4)
  A (*2)

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

%hint ShowX : Show X; ShowX = %runElab derive

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
