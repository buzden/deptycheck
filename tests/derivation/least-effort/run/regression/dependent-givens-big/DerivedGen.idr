module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  decEq PrimTy PrimTy = Yes Refl
  decEq PrimTy RefTy  = No $ \case Refl impossible
  decEq RefTy  PrimTy = No $ \case Refl impossible
  decEq RefTy  RefTy  = Yes Refl

Show AnyType where
  show PrimTy = "PrimTy"
  show RefTy  = "RefTy"

namespace MaybeAnyType

  -- specialisation since we don't support polymorphism over types yet
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

  public export
  Show MaybeAnyType where
    show Nothing  = "Nothing"
    show (Just x) = "Just \{show x}"

  export
  Injective MaybeAnyType.Just where
    injective Refl = Refl

  export
  DecEq MaybeAnyType where
    decEq Nothing  Nothing  = Yes Refl
    decEq Nothing  (Just _) = No $ \case Refl impossible
    decEq (Just _) Nothing  = No $ \case Refl impossible
    decEq (Just x) (Just y) = decEqCong $ decEq x y

namespace VectMaybeAnyType

  -- specialisation since we don't support polymorphism over types yet
  public export
  data VectMaybeAnyType : Nat -> Type where
    Nil  : VectMaybeAnyType Z
    (::) : MaybeAnyType -> VectMaybeAnyType n -> VectMaybeAnyType (S n)

  public export
  toVect : VectMaybeAnyType n -> Vect n MaybeAnyType
  toVect [] = []
  toVect (x::xs) = x :: toVect xs

  public export
  Show (VectMaybeAnyType n) where
    show = show . toVect

  public export
  index : Fin n -> VectMaybeAnyType n -> MaybeAnyType
  index FZ     (x::_ ) = x
  index (FS i) (_::xs) = index i xs

  export
  Biinjective VectMaybeAnyType.(::) where
    biinjective Refl = (Refl, Refl)

  export
  DecEq (VectMaybeAnyType n) where
    decEq []      []      = Yes Refl
    decEq (x::xs) (y::ys) = decEqCong2 (decEq x y) (decEq xs ys)

  public export
  data AtIndex : (n : Nat) -> Fin n -> MaybeAnyType -> VectMaybeAnyType n -> Type where
    Here  : AtIndex (S n) FZ x (x::xs)
    There : AtIndex n i x zs -> AtIndex (S n) (FS i) x (z::zs)

  export
  Show (AtIndex n i t vs) where
    show Here = "!"
    show (There x) = "." ++ show x

%language ElabReflection

checkedGen : Fuel -> (n : Nat) -> (v : VectMaybeAnyType n) -> Gen MaybeEmpty (i ** t ** AtIndex n i t v)
checkedGen = deriveGen @{LeastEffort}

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl 3 [Nothing, Just PrimTy, Just RefTy]
  , G $ \fl => checkedGen fl 0 []
  ]
