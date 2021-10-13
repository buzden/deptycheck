module Test.DepTyCheck.Gen.Auto.Util

import public Data.Fin
import public Data.List.Lazy
import public Data.Vect.Dependent
import public Data.Zippable

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Language.Reflection.TTImp
import public Language.Reflection.Types

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

  public export %inline
  (.asVect) : (s : SortedSet a) -> Vect (s.asList.length) a
  s.asVect = fromList s.asList

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

-----------------------------------------------
--- `Language.Reflection`-related utilities ---
-----------------------------------------------

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

public export
appFuel : (topmost : Name) -> (fuel : TTImp) -> TTImp
appFuel = app . var

public export
liftList : List TTImp -> TTImp
liftList = foldr (\l, r => `(~(l) :: ~(r))) `([])

--- General purpose instances ---

public export
Eq Namespace where
  MkNS xs == MkNS ys = xs == ys

public export
Eq UserName where
  Basic x    == Basic y    = x == y
  Field x    == Field y    = x == y
  Underscore == Underscore = True
  _ == _ = False

public export
Eq Name where
  UN x   == UN y   = x == y
  MN x n == MN y m = x == y && n == m
  NS s n == NS p m = s == p && n == m
  DN x n == DN y m = x == y && n == m

  Nested x n    ==  Nested y m   = x == y && n == m
  CaseBlock x n == CaseBlock y m = x == y && n == m
  WithBlock x n == WithBlock y m = x == y && n == m

  _ == _ = False

--- Working around primitive values ---

export
primTypeInfo : String -> TypeInfo
primTypeInfo s = MkTypeInfo (UN $ Basic s) [] []

export
typeInfoOfConstant : Constant -> Maybe TypeInfo
typeInfoOfConstant (I _)       = Nothing
typeInfoOfConstant (BI _)      = Nothing
typeInfoOfConstant (I8 _)      = Nothing
typeInfoOfConstant (I16 _)     = Nothing
typeInfoOfConstant (I32 _)     = Nothing
typeInfoOfConstant (I64 _)     = Nothing
typeInfoOfConstant (B8 _)      = Nothing
typeInfoOfConstant (B16 _)     = Nothing
typeInfoOfConstant (B32 _)     = Nothing
typeInfoOfConstant (B64 _)     = Nothing
typeInfoOfConstant (Str _)     = Nothing
typeInfoOfConstant (Ch _)      = Nothing
typeInfoOfConstant (Db _)      = Nothing
typeInfoOfConstant WorldVal    = Nothing
typeInfoOfConstant IntType     = Just $ primTypeInfo "Int"
typeInfoOfConstant IntegerType = Just $ primTypeInfo "Integer"
typeInfoOfConstant Int8Type    = Just $ primTypeInfo "Int8"
typeInfoOfConstant Int16Type   = Just $ primTypeInfo "Int16"
typeInfoOfConstant Int32Type   = Just $ primTypeInfo "Int32"
typeInfoOfConstant Int64Type   = Just $ primTypeInfo "Int64"
typeInfoOfConstant Bits8Type   = Just $ primTypeInfo "Bits8"
typeInfoOfConstant Bits16Type  = Just $ primTypeInfo "Bits16"
typeInfoOfConstant Bits32Type  = Just $ primTypeInfo "Bits32"
typeInfoOfConstant Bits64Type  = Just $ primTypeInfo "Bits64"
typeInfoOfConstant StringType  = Just $ primTypeInfo "String"
typeInfoOfConstant CharType    = Just $ primTypeInfo "Char"
typeInfoOfConstant DoubleType  = Just $ primTypeInfo "Double"
typeInfoOfConstant WorldType   = Nothing

--- Analyzing dependently typed signatures ---

export
argDeps : (args : List NamedArg) -> DVect args.length $ SortedSet . Fin . Fin.finToNat
