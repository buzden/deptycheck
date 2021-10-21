module Test.DepTyCheck.Gen.Auto.Util.Nat

import public Data.Fin

public export
(-) : (n : Nat) -> Fin n -> Nat
(-) n@(S _) FZ     = n
(-) (S k)   (FS x) = k - x

export
plus_discards_minus : (n : Nat) -> (f : Fin n) -> (n - f) + finToNat f = n
plus_discards_minus (S k) FZ     = rewrite plusZeroRightNeutral k in Refl
plus_discards_minus (S k) (FS x) = rewrite sym $ plusSuccRightSucc (k - x) (finToNat x) in
                                   rewrite plus_discards_minus k x in
                                   Refl
