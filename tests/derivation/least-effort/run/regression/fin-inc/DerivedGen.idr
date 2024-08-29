module DerivedGen

import RunDerivedGen

%default total

record FinInc n where
  constructor MkFinInc
  val : Nat
  prf : LTE val n

Show (FinInc n) where
  show (MkFinInc v p) = "MkFinInc \{show v} prf"

checkedGen : Fuel -> Gen MaybeEmpty (n ** FinInc n)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
