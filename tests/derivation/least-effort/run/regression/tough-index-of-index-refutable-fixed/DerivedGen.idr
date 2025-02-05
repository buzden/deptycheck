module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data Y : Bool -> Type where
  Z : Y x
  S : Y x -> Y x'

Show (Y b) where
  show = show . toNat where
    toNat : forall b. Y b -> Nat
    toNat Z = Z
    toNat (S x) = S (toNat x)

data X : Y True -> Y True -> Type where
  MkX : X a (S a)

[Xab] {a, b : _} -> Show (X a b) where
  show MkX = "MkX : X \{show a} \{show b}"

checkedGen : Fuel -> (a, b : Y True) -> Gen MaybeEmpty (X a b)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G @{Xab} $ \fl => checkedGen fl (S {x=False} Z) Z
  , G @{Xab} $ \fl => checkedGen fl Z Z
  , G @{Xab} $ \fl => checkedGen fl Z (S {x=False} Z)
  , G @{Xab} $ \fl => checkedGen fl (S {x=False} Z) (S {x=False} $ S {x=False} Z)
  ]
