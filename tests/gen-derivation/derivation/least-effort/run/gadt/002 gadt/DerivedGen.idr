module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

checkedGen : Fuel -> Gen (n ** Fin n)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
