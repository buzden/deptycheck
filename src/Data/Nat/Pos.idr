module Data.Nat.Pos

import public Data.Nat
import public Data.DPair
import Data.List1

%default total

public export %inline
PosNat : Type
PosNat = Subset Nat IsSucc

public export %inline
(+) : PosNat -> PosNat -> PosNat
Element (S n) _ + Element (S m) _ = Element (S n + S m) ItIsSucc

public export %inline
(*) : PosNat -> PosNat -> PosNat
Element (S n) _ * Element (S m) _ = Element (S n * S m) ItIsSucc

public export
toPosNat : Nat -> Maybe PosNat
toPosNat Z       = Nothing
toPosNat k@(S _) = Just $ Element k ItIsSucc

export
gcd : (a, b : Nat) -> {auto 0 ok : Either (IsSucc a) (IsSucc b)} -> PosNat
gcd Z Z       = void $ absurd ok
gcd a@(S _) Z = Element a ItIsSucc
gcd Z b@(S _) = Element b ItIsSucc
gcd a (S b)   = assert_total $ gcd (S b) (modNatNZ a (S b) SIsNonZero)

--- Working with weighted lists ---

export
pickWeighted : List1 (PosNat, a) -> Nat -> a
pickWeighted ((_, x):::[])                  _ = x
pickWeighted w@((Element n _, x):::(y::ys)) k = if k < n then x else pickWeighted (assert_smaller w $ y:::ys) (k `minus` n)

foldmne : Foldable f => (a -> a -> a) -> f a -> Maybe a
foldmne g = foldl gg Nothing where
  gg : Maybe a -> a -> Maybe a
  gg ml r = ml <&> \l => g l r

export
normaliseWeights : Foldable f => Functor f => f (PosNat, a) -> f (PosNat, a)
normaliseWeights xs = do
  let Just $ Element (S d) _ = foldmne gcd' $ Builtin.fst <$> xs
    | Nothing => xs
  flip map xs $ mapFst $ \(Element n _) => Element (divNatNZ n (S d) SIsNonZero) (believe_me $ ItIsSucc {n=1} {- since divisor is GCD -})
  where
    gcd' : (a, b : PosNat) -> PosNat
    gcd' (Element n _) (Element m _) = gcd n m
