module Data.SnocVect

import Data.Vect
import Data.Nat

public export
data SnocVect : (len : Nat) -> (elem : Type) -> Type where
  Lin : SnocVect 0 e
  (:<) : SnocVect n e -> e -> SnocVect (S n) e

fromVect' : SnocVect l' e -> Vect l'' e -> SnocVect (l' + l'') e
fromVect' x [] = rewrite plusZeroRightNeutral l' in x
fromVect' y (x :: xs) = do
  let fvv = fromVect' (y :< x) xs
  let 0 psrs = sym $ plusSuccRightSucc l' _
  rewrite__impl (flip SnocVect e) psrs fvv


public export
fromVect : Vect l e -> SnocVect l e
fromVect v = fromVect' [<] v

toVect' : Vect l' e -> SnocVect l'' e -> Vect (l' + l'') e
toVect' x [<] = rewrite plusZeroRightNeutral l' in x
toVect' x (y :< z) = do
  let fvv = toVect' (z :: x) y
  let 0 psrs = sym $ plusSuccRightSucc l' _
  rewrite__impl (flip Vect e) psrs fvv

public export
toVect : SnocVect l e -> Vect l e
toVect sv = toVect' [] sv

public export
fromSnocList : (sl : SnocList e) -> SnocVect (length sl) e
fromSnocList [<] = [<]
fromSnocList (sx :< x) = fromSnocList sx :< x

public export
toSnocList : SnocVect l e -> SnocList e
toSnocList [<] = [<]
toSnocList (sx :< x) = toSnocList sx :< x

public export
Show e => Show (SnocVect l e) where
  show [<] = "[<]"
  show (xs :< x) = showHelper xs x ++ "]"
    where
      showHelper : Show ee => SnocVect ll ee -> ee -> String
      showHelper [<] y = "[" ++ show y
      showHelper (xs :< x) y = showHelper xs x ++ show y

public export
Functor (SnocVect l) where
  map f [<] = [<]
  map f (xs :< x) = map f xs :< f x

public export
Zippable (SnocVect l) where
  zipWith f [<] [<] = [<]
  zipWith f (xs :< x) (ys :< y) = zipWith f xs ys :< f x y
  unzipWith f [<] = ([<], [<])
  unzipWith f (xs :< x) = let (a, b) = f x; (as, bs) = unzipWith f xs in (as :< a, bs :< b)

public export
(++) : SnocVect a e -> SnocVect b e -> SnocVect (a + b) e
(++) a b = fromVect' a (toVect b)
