module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%language ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

ProbabilityTuning `{DerivedGen.(::)}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = 1

checkedGen : Fuel -> Gen MaybeEmpty ListNat
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show ListNat where
  show = show . toList where
    toList : ListNat -> List Nat
    toList []      = []
    toList (x::xs) = x :: toList xs

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
