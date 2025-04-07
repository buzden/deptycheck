module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

data Z : Fin n -> Fin m -> Type where
  MkZ : Z {n = S n} {m = 2} 0 1

checkedGen : Fuel -> (m : _) -> (g : Fin m) -> {n : _} -> (f : Fin n) -> Gen MaybeEmpty $ Z f g
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (Z a b) where
  show _ = "MkZ"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 2 1 {n=4} 0
  , G $ \fl => checkedGen fl 3 1 {n=2} 0
  ]
