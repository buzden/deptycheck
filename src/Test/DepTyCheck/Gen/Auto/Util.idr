module Test.DepTyCheck.Gen.Auto.Util

import public Data.Fin
import public Data.List.Lazy
import public Data.Zippable

import public Data.SortedMap
import public Data.SortedSet

import public Language.Reflection.TTImp

%default total

----------------------------
--- Function composition ---
----------------------------

infixl 0 .|

-- Instead of `f (a b) $ c d` or `f (a b) (c d)` you can write `f .| a b .| c d`
public export %inline
(.|) : (a -> b) -> a -> b
(.|) = id

-----------------------------
--- Nice postfix notation ---
-----------------------------

public export %inline
(.length) : List a -> Nat
xs.length = length xs

namespace SortedMap

  public export %inline
  (.asList) : SortedMap k v -> List (k, v)
  m.asList = SortedMap.toList m

namespace SortedSet

  public export %inline
  (.asList) : SortedSet a -> List a
  s.asList = SortedSet.toList s

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

---------------------------------
--- `TTImp`-related utilities ---
---------------------------------

--- Parsing `TTImp` stuff ---

public export
unDPair : TTImp -> (List (Count, PiInfo TTImp, Maybe Name, TTImp), TTImp)
unDPair (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) typ) (ILam _ cnt piInfo mbname _ lamTy)) =
    mapFst ((cnt, piInfo, mbname, typ)::) $ unDPair lamTy
unDPair expr = ([], expr)

--- General purpose instances ---

public export
Eq Namespace where
  MkNS xs == MkNS ys = xs == ys

public export
Eq Name where
  UN x   == UN y   = x == y
  MN x n == MN y m = x == y && n == m
  NS s n == NS p m = s == p && n == m
  DN x n == DN y m = x == y && n == m
  RF x   == RF y   = x == y
  _ == _ = False
