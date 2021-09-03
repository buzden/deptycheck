module Test.DepTyCheck.Gen.Auto.Util

import public Data.Fin
import public Data.List.Lazy
import public Data.Zippable

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Language.Reflection.TTImp
import public Language.Reflection.Syntax

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

public export
mapI' : (xs : List a) -> (Fin xs.length -> a -> b) -> List b
mapI' []      _ = []
mapI' (x::xs) f = f FZ x :: mapI' xs (f . FS)

public export
mapMaybeI' : (xs : List a) -> (Fin xs.length -> a -> Maybe b) -> List b
mapMaybeI' []      _ = []
mapMaybeI' (x::xs) f = maybe id (::) .| f FZ x .| mapMaybeI' xs (f . FS)

-----------------------------
--- `SortedMap` utilities ---
-----------------------------

namespace SortedMap

  export
  mapMaybe : Ord k => (a -> Maybe b) -> SortedMap k a -> SortedMap k b
  mapMaybe f = SortedMap.fromList . mapMaybe (\(k, a) => (k,) <$> f a) . SortedMap.toList

---------------------------------
--- `TTImp`-related utilities ---
---------------------------------

--- Parsing and rebuilding `TTImp` stuff ---

public export
unDPair : TTImp -> (List (Arg False), TTImp)
unDPair (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) typ) (ILam _ cnt piInfo mbname _ lamTy)) =
    mapFst (MkArg cnt piInfo mbname typ ::) $ unDPair lamTy
unDPair expr = ([], expr)

public export
buildDPair : (rhs : TTImp) -> List (Name, TTImp) -> TTImp
buildDPair = foldr $ \(name, type), res =>
  var `{Builtin.DPair.DPair} .$ type .$ lam (MkArg MW ExplicitArg (Just name) type) res

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

  Nested x n    ==  Nested y m   = x == y && n == m
  CaseBlock x n == CaseBlock y m = x == y && n == m
  WithBlock x n == WithBlock y m = x == y && n == m

  _ == _ = False

-------------------------------------------
--- Reflection-related additional stuff ---
-------------------------------------------

-- Workaround of some type inference bug
public export
argName : Arg True -> Name
argName = name
