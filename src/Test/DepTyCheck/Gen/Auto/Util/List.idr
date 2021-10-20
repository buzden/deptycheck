module Test.DepTyCheck.Gen.Auto.Util.List

import public Data.List.Lazy
import public Data.Vect.Dependent

import public Test.DepTyCheck.Gen.Auto.Util.Syntax

%default total

-----------------------
--- Lists utilities ---
-----------------------

-- Calculates all pairs except for the pairs of elements with themselves.
public export
notTrivPairs : List a -> LazyList (a, a)
notTrivPairs []      = empty
notTrivPairs (x::xs) = (x,) <$> fromList xs <|> notTrivPairs xs

public export
findDiffPairWhich : (a -> a -> Bool) -> List a -> LazyList (a, a)
findDiffPairWhich p = filter (uncurry p) . notTrivPairs

public export
findPairWhich : (a -> b -> Bool) -> List a -> List b -> LazyList (a, b)
findPairWhich p xs ys = filter (uncurry p) $ fromList xs `zip` fromList ys

public export %inline
toNatList : Foldable f => f (Fin n) -> List Nat
toNatList = map finToNat . toList

public export
mapI' : (xs : List a) -> (Fin xs.length -> a -> b) -> List b
mapI' []      _ = []
mapI' (x::xs) f = f FZ x :: mapI' xs (f . FS)

public export
mapMaybeI' : (xs : List a) -> (Fin xs.length -> a -> Maybe b) -> List b
mapMaybeI' []      _ = []
mapMaybeI' (x::xs) f = maybe id (::) .| f FZ x .| mapMaybeI' xs (f . FS)

export
inits' : (xs : List a) -> DVect xs.length $ \idx => Vect (S $ finToNat idx) a
inits' []      = []
inits' (x::xs) = [x] :: ((x ::) <$> inits' xs)

export
toListI : Vect n a -> List (a, Fin n)
toListI []      = []
toListI (x::xs) = (x, FZ) :: (map FS <$> toListI xs)
