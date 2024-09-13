module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data IsFS : (n : _) -> Fin n -> Type where
  ItIsFS : IsFS _ (FS i)

Show (IsFS n vs) where show ItIsFS = "ItIsFS"

%language ElabReflection

checkedGen : Fuel -> (n : Nat) -> Gen MaybeEmpty (v ** IsFS n v)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 3
  , G $ \fl => checkedGen fl 0
  ]
