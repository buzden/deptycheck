module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data EqNat : Nat -> Nat -> Type where
  MkEqNat : a === b -> EqNat a b

Show (EqNat a b) where
  show _ = "Refl"

export
checkedGen : Fuel -> (a, b : Nat) -> Gen (EqNat a b) -- Gen (a = b)
checkedGen = deriveGen

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 0 0
  , G $ \fl => checkedGen fl 0 1
  , G $ \fl => checkedGen fl 18 18
  , G $ \fl => checkedGen fl 18 0
  , G $ \fl => checkedGen fl 18 17
  ]
