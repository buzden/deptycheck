module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

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
  data AtIndex : Fin n -> MaybeAnyType -> VectMaybeAnyType n -> Type where
    Here  : AtIndex FZ x (x::xs)
    There : {n : Nat} -> {0 i : Fin n} -> {0 zs : VectMaybeAnyType n} ->
            AtIndex i x zs -> AtIndex (FS i) x (z::zs)

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {n : Nat} -> (v : VectMaybeAnyType n) -> Gen MaybeEmpty (i ** t ** AtIndex i t v)
