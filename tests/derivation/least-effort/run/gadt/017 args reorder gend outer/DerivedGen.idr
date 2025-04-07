module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

data Z : Fin n -> Fin m -> Type where
  MkZ : Z {n = S n} {m = 2} 0 1

checkedGen : Fuel -> Gen MaybeEmpty (m ** g : Fin m ** n ** f : Fin n ** Z f g)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (Z a b) where
  show _ = "MkZ"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl
  ]
