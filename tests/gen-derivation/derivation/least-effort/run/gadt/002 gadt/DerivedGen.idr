module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

checkedGen : Fuel -> Gen CanBeEmptyStatic (n ** Fin n)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
