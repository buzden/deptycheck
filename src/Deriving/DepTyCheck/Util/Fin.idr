module Deriving.DepTyCheck.Util.Fin

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

--- Fin of sum ---

public export
indexSum : {m : Nat} -> Either (Fin m) (Fin n) -> Fin (m + n)
indexSum (Left  l) = weakenN n l
indexSum (Right r) = shift m r

public export
splitSum : {m : Nat} -> Fin (m + n) -> Either (Fin m) (Fin n)
splitSum {m=Z}   k      = Right k
splitSum {m=S m} FZ     = Left FZ
splitSum {m=S m} (FS k) = mapFst FS $ splitSum k

--- Collections of `Fin`s ---

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
