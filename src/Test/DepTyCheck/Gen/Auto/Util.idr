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

export
inits' : (xs : List a) -> DVect xs.length $ \idx => Vect (S $ finToNat idx) a
inits' []      = []
inits' (x::xs) = [x] :: ((x ::) <$> inits' xs)

export
toListI : Vect n a -> List (a, Fin n)
toListI []      = []
toListI (x::xs) = (x, FZ) :: (map FS <$> toListI xs)

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

-- IMPORTANT NOTE: this is only an approximation
dependsOnName : TTImp -> Name -> Bool
dependsOnName = assert_total $ flip depTTImp where mutual
  %default covering -- well, I don't know why those functions below do not pass termination check...

  unAutoMN : Name -> Name
  unAutoMN (MN s 0) = UN $ Basic s
  unAutoMN n        = n

  depTTImp : Name -> TTImp -> Bool
  depTTImp sn $ IVar _ n                  = n == sn
  depTTImp sn $ IPi _ _ _ mn _ retTy      = (unAutoMN <$> mn) /= Just sn && depTTImp sn retTy
  depTTImp sn $ ILam _ _ _ mn _ lamTy     = (unAutoMN <$> mn) /= Just sn && depTTImp sn lamTy
  depTTImp sn $ ILet _ _ _ n _ nVal scope = depTTImp sn nVal || n /= sn && depTTImp sn scope
  depTTImp sn $ ICase _ expr _ cls        = depTTImp sn expr || any (depClause sn) cls
  depTTImp sn $ ILocal _ decls expr       = depTTImp sn expr -- to consider if `decls` override the `sn` name
  depTTImp sn $ IUpdate _ upds expr       = any (depFieldUpdate sn) upds || depTTImp sn expr
  depTTImp sn $ IApp _ l r                = depTTImp sn l || depTTImp sn r
  depTTImp sn $ INamedApp _ l _ r         = depTTImp sn l || depTTImp sn r
  depTTImp sn $ IAutoApp _ l r            = depTTImp sn l || depTTImp sn r
  depTTImp sn $ IWithApp _ l r            = depTTImp sn l || depTTImp sn r
  depTTImp sn $ ISearch _ _               = False
  depTTImp sn $ IAlternative _ _ alts     = any (depTTImp sn) alts -- very rough approximation, but what can I do?
  depTTImp sn $ IRewrite _ e f            = depTTImp sn e || depTTImp sn f
  depTTImp sn $ IBindHere _ _ e           = depTTImp sn e
  depTTImp sn $ IBindVar _ n              = UN (Basic n) == sn
  depTTImp sn $ IAs _ _ _ n e             = n == sn || depTTImp sn e
  depTTImp sn $ IMustUnify _ _ e          = depTTImp sn e
  depTTImp sn $ IDelayed _ _ e            = depTTImp sn e
  depTTImp sn $ IDelay _ e                = depTTImp sn e
  depTTImp sn $ IForce _ e                = depTTImp sn e
  depTTImp sn $ IQuote _ e                = False -- this is too rough
  depTTImp sn $ IQuoteName _ n            = False
  depTTImp sn $ IQuoteDecl _ decls        = False -- this is too rough
  depTTImp sn $ IUnquote _ e              = depTTImp sn e
  depTTImp sn $ IPrimVal _ _              = False
  depTTImp sn $ IType _                   = False
  depTTImp sn $ IHole _ _                 = False
  depTTImp sn $ Implicit _ _              = False
  depTTImp sn $ IWithUnambigNames _ ns e  = depTTImp sn e -- I have no idea what's going on here

  depClause : Name -> Clause -> Bool
  depClause sn $ PatClause _ lhs rhs              = not (depTTImp sn lhs) && depTTImp sn rhs
  depClause sn $ WithClause _ lhs wval prfn _ cls = not (depTTImp sn lhs) && not (depTTImp sn wval) && prfn /= Just sn && any (depClause sn) cls
  depClause sn $ ImpossibleClause _ _             = False

  depFieldUpdate : Name -> IFieldUpdate -> Bool
  depFieldUpdate sn (ISetField    _ expr) = depTTImp sn expr
  depFieldUpdate sn (ISetFieldApp _ expr) = depTTImp sn expr

export
argDeps : (args : List NamedArg) -> DVect args.length $ SortedSet . Fin . Fin.finToNat
argDeps args = inits' args <&> \ar => oneArg .| last ar .| init ar where
  oneArg : forall n. NamedArg -> Vect n NamedArg -> SortedSet $ Fin n
  oneArg arg = fromList . map snd . filter (dependsOnName arg.type . name . fst) . toListI
