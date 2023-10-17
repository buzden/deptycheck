module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Type

data Y : X -> Type where
  MkY : Y x

data X : Type where
  Nil : X
  Cons : (x : X) -> Y x -> X

data Z : X -> X -> Type where
  MkZ : (prf : Y x) -> Z (Cons x prf) (Cons x prf)

Show (Y x) where
  show MkY = "MkY"

Show X where
  show Nil = "Nil"
  show (Cons x y) = "Cons (\{show x}) (\{show y})"

Show (Z a b) where
  show (MkZ prf) = "MkZ (\{show prf})"

DecEq (Y x) where
  decEq MkY MkY = Yes Refl

DecEq X where
  decEq Nil Nil = Yes Refl
  decEq Nil (Cons _ _) = No $ \case Refl impossible
  decEq (Cons _ _) Nil = No $ \case Refl impossible
  decEq (Cons x xs) (Cons y ys) with (decEq x y)
    _                             | No c     = No $ \Refl => c Refl
    decEq (Cons x xs) (Cons x ys) | Yes Refl with (decEq xs ys)
      decEq (Cons x xs) (Cons x xs) | Yes Refl | Yes Refl = Yes Refl
      decEq (Cons x xs) (Cons x ys) | Yes Refl | No c     = No $ \Refl => c Refl

%language ElabReflection

checkedGen : Fuel -> (x : X) -> (x' : X) -> Gen MaybeEmpty $ Z x x'
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl Nil Nil
  , G $ \fl => checkedGen fl Nil (Cons Nil MkY)
  , G $ \fl => checkedGen fl (Cons Nil MkY) (Cons Nil MkY)
  , G $ \fl => checkedGen fl ((Nil `Cons` MkY) `Cons` MkY) ((Nil `Cons` MkY) `Cons` MkY)
  ]
