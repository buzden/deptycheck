module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

data Z : Fin n -> Fin m -> Type where
  MkZ : Z {n = S n} {m = 2} 0 1

data X = MkX (Z {n=3} {m=2} 0 1)

checkedGen : Fuel -> (Fuel -> (m : _) -> (g : Fin m) -> {n : _} -> (f : Fin n) -> Gen MaybeEmpty $ Z f g) => Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show X where
  show _ = "MkX"

genZ : Fuel -> (m : _) -> (g : Fin m) -> {n : _} -> (f : Fin n) -> Gen MaybeEmpty $ Z f g
genZ = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{genZ}
  ]
