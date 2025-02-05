module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data Y : Unit -> Type where
  Z : Y x
  S : Y x -> Y x'

Injective (DerivedGen.S) where
  injective Refl = Refl

DecEq (Y ()) where
  decEq Z Z = Yes Refl
  decEq (S {x=MkUnit} x) (S {x=MkUnit} x') = decEqCong $ decEq x x'
  decEq Z (S _) = No $ \case Refl impossible
  decEq (S _) Z = No $ \case Refl impossible

Show (Y b) where
  show = show . toNat where
    toNat : forall b. Y b -> Nat
    toNat Z = Z
    toNat (S x) = S (toNat x)

data X : Y () -> Y () -> Type where
  MkX : X a (S a)

[Xab] {a, b : _} -> Show (X a b) where
  show MkX = "MkX : X \{show a} \{show b}"

checkedGen : Fuel -> (a, b : Y ()) -> Gen MaybeEmpty (X a b)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [ G @{Xab} $ \fl => checkedGen fl (S {x=()} Z) Z
  , G @{Xab} $ \fl => checkedGen fl Z Z
  , G @{Xab} $ \fl => checkedGen fl Z (S {x=()} Z)
  , G @{Xab} $ \fl => checkedGen fl (S {x=()} Z) (S {x=()} $ S {x=()} Z)
  ]
