module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

checkedGen : Fuel -> (n : Nat) -> Gen MaybeEmpty $ Fin n
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 1
  , G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 5
  ]
