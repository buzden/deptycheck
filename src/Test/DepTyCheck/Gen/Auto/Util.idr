module Test.DepTyCheck.Gen.Auto.Util

import public Data.Fin
import public Data.List.Lazy
import public Data.Zippable

%default total

-----------------------
--- Lists utilities ---
-----------------------

public export %inline
(.length) : List a -> Nat
xs.length = length xs

-- Not effective but clean
public export
find' : (p : a -> Bool) -> (xs : List a) -> Maybe $ Fin xs.length
find' _ [] = Nothing
find' p (x::xs) = if p x then Just FZ else FS <$> find' p xs

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
