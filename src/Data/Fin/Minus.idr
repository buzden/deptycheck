||| Special subtraction of a `Fin` from a `Nat`
module Data.Fin.Minus

import public Data.Fin

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
