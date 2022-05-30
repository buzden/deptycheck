module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

data X = MkX (Maybe Bool)

%runElab derive "X" [Generic, Meta, Show]

checkedGen : Fuel -> Gen X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
