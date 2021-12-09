module Test.DepTyCheck.Gen.Auto.Util.Fin

import public Data.Vect

--- Special subtraction ---

public export
(-) : (n : Nat) -> Fin (S n) -> Nat
n   - FZ   = n
S k - FS x = k - x

export
plus_discards_minus : (n : Nat) -> (f : Fin $ S n) -> (n - f) + finToNat f = n
plus_discards_minus k     FZ     = rewrite plusZeroRightNeutral k in Refl
plus_discards_minus (S k) (FS x) = rewrite sym $ plusSuccRightSucc (k - x) (finToNat x) in
                                   rewrite plus_discards_minus k x in
                                   Refl

export
minus_last_gives_0 : (n : Nat) -> n - Fin.last = 0
minus_last_gives_0 Z     = Refl
minus_last_gives_0 (S k) = minus_last_gives_0 k

--- Collections of `Fin`s ---

public export
allFins' : {n : Nat} -> Vect n (Fin n)
allFins' {n=Z  } = []
allFins' {n=S k} = FZ :: map FS allFins'

public export
rangeFrom0To : Fin n -> List (Fin n)
rangeFrom0To FZ     = [FZ]
rangeFrom0To (FS x) = FZ :: (FS <$> rangeFrom0To x)

public export
rangeFromTo : Fin n -> Fin n -> List (Fin n)
rangeFromTo FZ     FZ     = [FZ]
rangeFromTo FZ     r      = rangeFrom0To r
rangeFromTo l      FZ     = reverse $ rangeFrom0To l
rangeFromTo (FS l) (FS r) = FS <$> rangeFromTo l r

export
allGreaterThan : {n : _} -> Fin n -> List (Fin n)
allGreaterThan curr = case strengthen $ FS curr of
                        Nothing => []
                        Just next => next :: allGreaterThan (assert_smaller curr next) -- `next` is closer to the upper bound than `curr`

--- Conversions of `Fin`s ---

public export
tryToFit : {to : _} -> Fin from -> Maybe $ Fin to
tryToFit {to=0}   _      = Nothing
tryToFit {to=S _} FZ     = Just FZ
tryToFit {to=S _} (FS x) = FS <$> tryToFit x

public export
weakenToSuper : {i : Fin n} -> Fin (finToNat i) -> Fin n
weakenToSuper {i = FS _} FZ     = FZ
weakenToSuper {i = FS _} (FS x) = FS $ weakenToSuper x

export
weakenToSuper_correct : {i : Fin n} -> (x : Fin $ finToNat i) -> finToNat (weakenToSuper {i} x) = finToNat x
weakenToSuper_correct {i = FS _} FZ     = Refl
weakenToSuper_correct {i = FS _} (FS x) = cong S $ weakenToSuper_correct x

--- Min/max stuff ---

public export
min : Fin n -> Fin n -> Fin n
min FZ     _      = FZ
min (FS _) FZ     = FZ
min (FS l) (FS r) = FS $ min l r

public export
max : Fin n -> Fin n -> Fin n
max FZ       r      = r
max l@(FS _) FZ     = l
max (FS l)   (FS r) = FS $ max l r

namespace Semigroup

  public export
  [Minimum] Semigroup (Fin n) where
    (<+>) = Fin.min

  public export
  [Maximum] Semigroup (Fin n) where
    (<+>) = Fin.max

namespace Monoid

  public export
  [Minimum] {n : Nat} -> Monoid (Fin $ S n) using Fin.Semigroup.Minimum where
    neutral = last

  public export
  [Maximum] Monoid (Fin $ S n) using Fin.Semigroup.Maximum where
    neutral = FZ
