module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data IsFS : (n : _) -> Fin n -> Type where
  ItIsFS : IsFS (S _) (FS i)

Show (IsFS n vs) where show ItIsFS = "ItIsFS"

%language ElabReflection

checkedGen : Fuel -> {n : Nat} -> (v : Fin n) -> Gen MaybeEmpty $ IsFS n v
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl $ the (Fin 4) 3
  , G $ \fl => checkedGen fl $ the (Fin 3) 0
  ]
