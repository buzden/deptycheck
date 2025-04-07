module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%language ElabReflection

data Z : Fin n -> Fin m -> Type where
  MkZ : Z {n = S n} {m = 2} 0 1

data X = MkX (Z a b)

checkedGen : Fuel -> (Fuel -> Gen MaybeEmpty (m ** g : Fin m ** n ** f : Fin n ** Z f g)) => Gen MaybeEmpty X
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show X where
  show _ = "MkX"

genZ : Fuel -> Gen MaybeEmpty (m ** g : Fin m ** n ** f : Fin n ** Z f g)
genZ _ = pure (_ ** _ ** 5 ** _ ** MkZ)

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl @{genZ}
  ]
