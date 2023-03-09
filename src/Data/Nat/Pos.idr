module Data.Nat.Pos

import public Data.Nat
import public Data.DPair
import Data.CheckedEmpty.List.Lazy
import public Data.So

%default total

--- Type definition ---

public export %inline
PosNat : Type
PosNat = Subset Nat IsSucc

--- Literals syntax support ---

public export %inline
fromInteger : (x : Integer) -> (0 _ : So $ x >= 1) => PosNat
fromInteger x = Element (cast x) (believe_me $ ItIsSucc {n=1})

--- Simple arithmetics ---

public export %inline
(+) : PosNat -> PosNat -> PosNat
Element (S n) _ + Element (S m) _ = Element (S n + S m) ItIsSucc

public export %inline
(*) : PosNat -> PosNat -> PosNat
Element (S n) _ * Element (S m) _ = Element (S n * S m) ItIsSucc

--- Semigroups and etc ---

namespace Semigroup

  public export
  [ Additive ] Semigroup PosNat where
    (<+>) = (+)

  public export
  [ Multiplicative ] Semigroup PosNat where
    (<+>) = (*)

namespace Monoid

  public export
  Monoid PosNat using Pos.Semigroup.Multiplicative where
    neutral = 1

--- Covertions ---

public export
toPosNat : Nat -> Maybe PosNat
toPosNat Z       = Nothing
toPosNat k@(S _) = Just $ Element k ItIsSucc

--- Greatest common divisor ---

export
gcd : (a, b : Nat) -> {auto 0 ok : Either (IsSucc a) (IsSucc b)} -> PosNat
gcd Z Z       = void $ absurd ok
gcd a@(S _) Z = Element a ItIsSucc
gcd Z b@(S _) = Element b ItIsSucc
gcd a (S b)   = assert_total $ gcd (S b) (modNatNZ a (S b) SIsNonZero)

--- Working with weighted lists ---

export
pickWeighted : LazyLst1 (PosNat, a) -> Nat -> a
pickWeighted [(_, x)]                     _ = x
pickWeighted wh@((Element n _, x)::y::ys) k = if k < n then x else pickWeighted (assert_smaller wh $ y::ys) (k `minus` n)

foldmne : Foldable f => (a -> a -> a) -> f a -> Maybe a
foldmne g = foldl gg Nothing where
  gg : Maybe a -> a -> Maybe a
  gg ml r = (ml <&> \l => g l r) <|> Just r

export
normaliseWeights : Foldable f => Functor f => f (PosNat, a) -> f (PosNat, a)
normaliseWeights xs = do
  let Just $ Element (S d) _ = foldmne gcd' $ Builtin.fst <$> xs
    | Nothing => xs
  flip map xs $ mapFst $ \(Element n _) => Element (divNatNZ n (S d) SIsNonZero) (believe_me $ ItIsSucc {n=1} {- since divisor is GCD -})
  where
    gcd' : (a, b : PosNat) -> PosNat
    gcd' (Element n _) (Element m _) = gcd n m
