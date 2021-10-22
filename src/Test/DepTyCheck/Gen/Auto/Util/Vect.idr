module Test.DepTyCheck.Gen.Auto.Util.Vect

import public Data.Vect

import public Test.DepTyCheck.Gen.Auto.Util.Nat

export
toListI : Vect n a -> List (a, Fin n)
toListI []      = []
toListI (x::xs) = (x, FZ) :: (map FS <$> toListI xs)

public export
drop'' : (xs : Vect n a) -> (count : Fin $ S n) -> Vect (n - count) a
drop'' xs      FZ     = xs
drop'' (_::xs) (FS c) = drop'' xs c
