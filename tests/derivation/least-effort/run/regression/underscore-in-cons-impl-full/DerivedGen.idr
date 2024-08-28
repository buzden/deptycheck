module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data IsFS : Fin n -> Type where
  ItIsFS : IsFS (FS i)

Show (IsFS vs) where show ItIsFS = "ItIsFS"

%language ElabReflection

checkedGen : Fuel -> {n : Nat} -> (v : Fin n) -> Gen MaybeEmpty $ IsFS v
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl $ the (Fin 4) 3
  , G $ \fl => checkedGen fl $ the (Fin 3) 0
  ]
