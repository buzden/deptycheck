module DerivedGen

import RunDerivedGen

%default total

data Y : Maybe Unit -> Type where
  MkY : Y $ Just x

Show (Y mu) where show MkY = "MkY"

checkedGen : Fuel -> (c : _) -> Gen MaybeEmpty $ Y c
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl $ Nothing
  , G $ \fl => checkedGen fl $ Just ()
  ]
