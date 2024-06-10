module Data.Nat1

import public Data.Nat
import public Data.DPair
import Data.CheckedEmpty.List.Lazy
import public Data.So

%default total

--- Type definition ---

public export
data Nat1 : Type where
  FromNat : (n : Nat) -> (0 _ : IsSucc n) => Nat1

--- Covertions ---

public export
toNat1 : Nat -> Maybe Nat1
toNat1 Z       = Nothing
toNat1 k@(S _) = Just $ FromNat k

public export %inline
fromNat : (x : Nat) -> (0 _ : IsSucc x) => Nat1
fromNat = FromNat

public export %inline
toNat, (.asNat) : Nat1 -> Nat
toNat $ FromNat n = n
(.asNat) = toNat

--- Literals syntax support ---

public export %inline
fromInteger : (x : Integer) -> (0 _ : So $ x >= 1) => Nat1
fromInteger x = FromNat (cast x) @{believe_me $ ItIsSucc {n=1}}

export
Range Nat1 where
  rangeFrom fr = rangeFrom fr.asNat <&> \x => FromNat x @{believe_me $ ItIsSucc {n=1}}
  rangeFromThen fr th = rangeFromThen fr.asNat th.asNat <&> \x => FromNat x @{believe_me $ ItIsSucc {n=1}}
  rangeFromTo fr to = rangeFromTo fr.asNat to.asNat <&> \x => FromNat x @{believe_me $ ItIsSucc {n=1}}
  rangeFromThenTo fr th to = rangeFromThenTo fr.asNat th.asNat to.asNat <&> \x => FromNat x @{believe_me $ ItIsSucc {n=1}}

--- Simple arithmetics ---

public export %inline
succ : Nat1 -> Nat1
succ $ FromNat n = FromNat (S n)

public export %inline
one : Nat1
one = 1

public export %inline
(+) : Nat1 -> Nat1 -> Nat1
FromNat (S n) + FromNat (S m) = FromNat (S n + S m)

public export %inline
(*) : Nat1 -> Nat1 -> Nat1
FromNat (S n) * FromNat (S m) = FromNat (S n * S m)

--- Semigroups and etc ---

namespace Semigroup

  public export
  [ Additive ] Semigroup Nat1 where
    (<+>) = (+)

  public export
  [ Multiplicative ] Semigroup Nat1 where
    (<+>) = (*)

namespace Monoid

  public export
  Monoid Nat1 using Nat1.Semigroup.Multiplicative where
    neutral = 1

--- Greatest common divisor ---

export
gcd : (a, b : Nat) -> (0 ok : Either (IsSucc a) (IsSucc b)) => Nat1
gcd Z Z       = void $ absurd ok
gcd a@(S _) Z = FromNat a
gcd Z b@(S _) = FromNat b
gcd a (S b)   = assert_total $ gcd (S b) (modNatNZ a (S b) SIsNonZero)

export
gcd' : Nat1 -> Nat1 -> Nat1
gcd' (FromNat n) (FromNat m) = gcd n m

--- Working with weighted lists ---

export
pickWeighted : LazyLst1 (Nat1, a) -> Nat -> a
pickWeighted [(_, x)]                     _ = x
pickWeighted wh@((FromNat n, x)::y::ys) k = if k < n then x else pickWeighted (assert_smaller wh $ y::ys) (k `minus` n)

foldmne : Foldable f => (a -> a -> a) -> f a -> Maybe a
foldmne g = foldl gg Nothing where
  gg : Maybe a -> a -> Maybe a
  gg ml r = (ml <&> \l => g l r) <|> Just r

export
normaliseWeights : Foldable f => Functor f => f (Nat1, a) -> f (Nat1, a)
normaliseWeights xs = do
  let Just $ FromNat (S d) = foldmne gcd' $ Builtin.fst <$> xs
    | Nothing => xs
  flip map xs $ mapFst $ \(FromNat n) => FromNat (divNatNZ n (S d) SIsNonZero) @{believe_me $ ItIsSucc {n=1} {- since divisor is GCD -}}
