module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  XZ : X 0
  XS : X n -> X (S n)

%language ElabReflection

checkedGen : Fuel -> (n : _) -> Gen MaybeEmpty $ X n
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

toNat : X n -> Nat
toNat XZ = Z
toNat (XS x) = S (toNat x)

Show (X n) where
  show = show . toNat

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0
  , G $ \fl => checkedGen fl 8
  , G $ \fl => checkedGen fl 15000
  ]
