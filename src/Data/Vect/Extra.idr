module Data.Vect.Extra

import Data.Fin.Minus
import Data.List1
import Data.SortedMap
import Data.SortedSet
import Data.Vect

%default total

public export
mapI : (f : Fin n -> a -> b) -> Vect n a -> Vect n b
mapI f []      = []
mapI f (x::xs) = f FZ x :: mapI (f . FS) xs

export
toListI : Vect n a -> List (a, Fin n)
toListI []      = []
toListI (x::xs) = (x, FZ) :: (map FS <$> toListI xs)

export %inline
withIndex : Vect n a -> Vect n (Fin n, a)
withIndex = mapI (,)

public export
drop'' : (xs : Vect n a) -> (count : Fin $ S n) -> Vect (n - count) a
drop'' xs      FZ     = xs
drop'' (_::xs) (FS c) = drop'' xs c

export
mapPre : ((i : Fin n) -> Vect (finToNat i) b -> a -> b) -> Vect n a -> Vect n b
mapPre f []      = []
mapPre f (x::xs) = let y = f FZ [] x in y :: mapPre (\i, ys => f (FS i) (y::ys)) xs

export
fromMap : {n : _} -> SortedMap (Fin n) a -> Vect n (Maybe a)
fromMap = foldl (flip . uncurry $ \i => replaceAt i . Just) (replicate _ Nothing) . SortedMap.toList

export
presenceVect : {n : _} -> SortedSet (Fin n) -> Vect n Bool
presenceVect = tabulate . flip contains

public export
reverseMapping : Ord a => Vect n a -> SortedMap a $ List1 $ Fin n
reverseMapping = concat . mapI (\idx, x => singleton x $ singleton idx)
