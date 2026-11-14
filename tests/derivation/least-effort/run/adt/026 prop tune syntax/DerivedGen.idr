module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%language ElabReflection

data X = A | B | C

%runElab tuneProbability "A".dataCon (*2)
%runElab tuneProbability "B".dataCon (const 4)

checkedGen : Fuel -> Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

%hint ShowX : Show X; ShowX = %runElab derive

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
