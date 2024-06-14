module Data.List.Extra

import Data.Alternative
import Data.List
import Data.List.Lazy
import Data.Vect
import Data.Vect.Dependent

import Syntax.IHateParens

%default total

-- Calculates all pairs except for the pairs of elements with themselves.
public export
notTrivPairs : List a -> LazyList (a, a)
notTrivPairs []      = empty
notTrivPairs (x::xs) = (x,) <$> fromList xs <|> notTrivPairs xs

public export
findDiffPairWhich : (a -> a -> Bool) -> List a -> LazyList (a, a)
findDiffPairWhich p = filter (uncurry p) . notTrivPairs

public export
findConsequentsWhich : (a -> a -> Bool) -> List a -> LazyList (a, a)
findConsequentsWhich f xs =
  let xs = Lazy.fromList xs in
  case tail' xs of
    Nothing => []
    Just tl => filter .| uncurry f .| xs `zip` tl

public export
infixOf : Eq a => List a -> List a -> Maybe (List a, List a)
infixOf = map (map snd) .: infixOfBy (\x, y => if x == y then Just () else Nothing)

public export %inline
toNatList : Foldable f => f (Fin n) -> List Nat
toNatList = map finToNat . toList

public export
mapI : (xs : List a) -> (Fin xs.length -> a -> b) -> List b
mapI []      _ = []
mapI (x::xs) f = f FZ x :: mapI xs (f . FS)

public export
mapMaybeI : (xs : List a) -> (Fin xs.length -> a -> Maybe b) -> List b
mapMaybeI []      _ = []
mapMaybeI (x::xs) f = maybe id (::) .| f FZ x .| mapMaybeI xs (f . FS)

public export
filterI : (xs : List a) -> (Fin xs.length -> a -> Bool) -> List a
filterI []      _ = []
filterI (x::xs) f = let fxs = filterI xs $ f . FS in
                    if f FZ x then x :: fxs else fxs

public export
withIndex : (xs : List a) -> List (Fin xs.length, a)
withIndex []      = []
withIndex (x::xs) = (FZ, x) :: map (mapFst FS) (withIndex xs)

public export
drop' : (xs : List a) -> (count : Fin $ S xs.length) -> List a
drop' xs      FZ     = xs
drop' (_::xs) (FS c) = drop' xs c

export
inits' : (xs : List a) -> DVect xs.length $ \idx => Vect (S $ finToNat idx) a
inits' []      = []
inits' (x::xs) = [x] :: ((x ::) <$> inits' xs)

export
findLastIndex : (a -> Bool) -> (xs : List a) -> Maybe $ Fin xs.length
findLastIndex f []      = Nothing
findLastIndex f (x::xs) = FS <$> findLastIndex f xs <|> whenT (f x) FZ

export
zipV : (xs : List a) -> Vect xs.length b -> List (a, b)
zipV []      []      = []
zipV (x::xs) (y::ys) = (x, y) :: zipV xs ys

export infixr 6 `zipV` -- as `zip`

export
lengthConcat : (xs, ys : List a) -> length (xs ++ ys) = length xs + length ys
lengthConcat []      ys = Refl
lengthConcat (_::xs) ys = rewrite lengthConcat xs ys in Refl
