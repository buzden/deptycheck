module DerivedGen

import AlternativeCore
import PrintDerivation

import Data.Fin

%default total

data AnyType = PrimTy | RefTy

DecEq AnyType where
  decEq PrimTy PrimTy = Yes Refl
  decEq PrimTy RefTy  = No $ \case Refl impossible
  decEq RefTy  PrimTy = No $ \case Refl impossible
  decEq RefTy  RefTy  = Yes Refl

namespace MaybeAnyType

  -- specialisation since we don't support polymorphism over types yet
  public export
  data MaybeAnyType
    = Nothing
    | Just AnyType

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

%language ElabReflection

%runElab printDerived @{LeastEffort} $ Fuel -> (n : Nat) -> (v : VectMaybeAnyType n) -> Gen MaybeEmpty (i ** t ** AtIndex n i t v)
