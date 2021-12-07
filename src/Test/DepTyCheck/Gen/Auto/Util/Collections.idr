module Test.DepTyCheck.Gen.Auto.Util.Collections

import public Data.List
import public Data.List.Lazy
import public Data.List1
import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet
import public Data.Vect
import public Data.Vect.Dependent

import public Test.DepTyCheck.Gen.Auto.Util.Fin
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

public export
filterI' : (xs : List a) -> (Fin xs.length -> a -> Bool) -> List a
filterI' []      _ = []
filterI' (x::xs) f = let fxs = filterI' xs $ f . FS in
                     if f FZ x then x :: fxs else fxs

public export
drop' : (xs : List a) -> (count : Fin $ S xs.length) -> List a
drop' xs      FZ     = xs
drop' (_::xs) (FS c) = drop' xs c

export
inits' : (xs : List a) -> DVect xs.length $ \idx => Vect (S $ finToNat idx) a
inits' []      = []
inits' (x::xs) = [x] :: ((x ::) <$> inits' xs)

--- Transitive clojure stuff ---

export covering
transitiveClosureM : Monad m => Eq a => (a -> m $ List a) -> List a -> m $ List a
transitiveClosureM f xs = tr xs xs where
  tr : (curr : List a) -> (new : List a) -> m $ List a
  tr curr [] = pure curr
  tr curr st = do
    next <- join <$> for st f
    let new = filter (not . (`elem` curr)) next
    tr (curr ++ new) new

export covering
holdsOnAnyInTrCl : Monad m => Eq a => (a -> Bool) -> (a -> m $ List a) -> List a -> m Bool
holdsOnAnyInTrCl prop f xs = pure (any prop xs) || tr xs xs where
  tr : (curr : List a) -> (new : List a) -> m Bool
  tr curr [] = pure False
  tr curr st = do
    next <- join <$> for st f
    let new = filter (not . (`elem` curr)) next
    pure (any prop new) || tr (curr ++ new) new

------------------------
--- `Vect` utilities ---
------------------------

export
toListI : Vect n a -> List (a, Fin n)
toListI []      = []
toListI (x::xs) = (x, FZ) :: (map FS <$> toListI xs)

public export
drop'' : (xs : Vect n a) -> (count : Fin $ S n) -> Vect (n - count) a
drop'' xs      FZ     = xs
drop'' (_::xs) (FS c) = drop'' xs c

-----------------------------
--- `SortedMap` utilities ---
-----------------------------

namespace SortedMap

  export
  mapMaybe : Ord k => (a -> Maybe b) -> SortedMap k a -> SortedMap k b
  mapMaybe f = SortedMap.fromList . mapMaybe (\(k, a) => (k,) <$> f a) . SortedMap.toList

-----------------------------
--- `SortedSet` utilities ---
-----------------------------

-- Not really a functor's `map`, because map fusion law does not hold
export
mapIn : Ord b => (a -> b) -> SortedSet a -> SortedSet b
mapIn f = fromList . map f . SortedSet.toList

export
fromFoldable : Ord a => Foldable f => f a -> SortedSet a
fromFoldable = foldl (flip insert) empty

export
allPermutations : Ord a => SortedSet a -> List1 $ List a
allPermutations s = case fromList s.asList of
  Nothing => pure []
  Just ss => do
    e  <- ss
    es <- allPermutations $ assert_smaller s $ delete e s
    pure $ e :: es

public export
allPermutations' : Ord a => SortedSet a -> List $ List a
allPermutations' = forget . allPermutations
