module Test.DepTyCheck.Gen.Weight

import Data.Nat.Pos
import public Data.So

%default total

public export
data Weight sz = Abs sz | Sized (Nat -> sz)

-- TODO to add `FromInteger` implementation, as soon as interface is here and supports bounds of input values.

namespace Nat

  export
  fromInteger : (n : Integer) -> (0 _ : So $ n >= 0) => Weight Nat
  fromInteger x = Abs $ fromInteger x

  -- Weight that is most appropriate for simple recursive calls
  public export
  Size : Weight Nat
  Size = Sized S

  public export
  One : Weight Nat
  One = Abs 1

namespace PosNat

  export
  fromInteger : (n : Integer) -> (0 _ : So $ n >= 1) => Weight PosNat
  fromInteger x = Abs $ fromInteger x

  -- Weight that is most appropriate for simple recursive calls
  public export
  Size : Weight PosNat
  Size = Sized $ \n => Element (S n) ItIsSucc

  public export %inline
  One : Weight PosNat
  One = Abs 1

public export
Semigroup sz => Semigroup (Weight sz) where
  Abs x   <+> Abs y   = Abs   $ x <+> y
  Abs x   <+> Sized f = Sized $ (x <+>) . f
  Sized f <+> Abs y   = Sized $ (<+> y) . f
  Sized f <+> Sized g = Sized $ \w => f w <+> g w

public export
Monoid sz => Monoid (Weight sz) where
  neutral = Abs neutral

public export
weightAtSize : (size : Nat) -> Weight sz -> sz
weightAtSize _ $ Abs x   = x
weightAtSize n $ Sized f = f n
