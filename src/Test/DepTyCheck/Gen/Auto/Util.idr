module Test.DepTyCheck.Gen.Auto.Util

import public Data.Fin
import public Data.List.Lazy
import public Data.Zippable

import public Data.SortedMap
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
  _ == _ = False

public export
Ord Name where
  compare = comparing $ \case
    NS ns n                   => show ns ++ "." ++ show n
    UN x                      => "user " ++ x
    MN x y                    => "{" ++ x ++ ":" ++ show y ++ "}"
    DN str y                  => str ++ "@" ++ show y
    RF n                      => "." ++ n
    Nested (outer, idx) inner => show outer ++ ":" ++ show idx ++ ":" ++ show inner
    CaseBlock outer i         => "case block in " ++ show outer ++ "@" ++ show i
    WithBlock outer i         => "with block in " ++ show outer ++ "@" ++ show i

--- Conversion functions ---

mutual

  substPiInfo : SortedMap Name Name -> PiInfo TTImp -> PiInfo TTImp
  substPiInfo nn ImplicitArg     = ImplicitArg
  substPiInfo nn ExplicitArg     = ExplicitArg
  substPiInfo nn AutoImplicit    = AutoImplicit
  substPiInfo nn (DefImplicit x) = DefImplicit $ substNameBy nn x

  substClause : SortedMap Name Name -> Clause -> Clause

  -- This function may not preserve FCs correctly in the case when `from` and `to` names differ in length.
  export
  substNameBy : SortedMap Name Name -> TTImp -> TTImp
  substNameBy nn $ IVar x y                        = IVar x $ fromMaybe y $ lookup y nn
  substNameBy nn $ IPi x y z w argTy retTy         = IPi x y (substPiInfo nn z) w (substNameBy nn argTy) $ if isJust $ w >>= flip lookup nn
                                                            then retTy
                                                            else substNameBy nn retTy
  substNameBy nn $ ILam x y z w argTy lamTy        = ILam x y (substPiInfo nn z) w (substNameBy nn argTy) $ if isJust $ w >>= flip lookup nn
                                                            then lamTy
                                                            else substNameBy nn lamTy
  substNameBy nn $ ILet x lhsFC y z nTy nVal scope = ILet x lhsFC y z (substNameBy nn nTy) (substNameBy nn nVal) $ if isJust $ lookup z nn
                                                            then scope
                                                            else substNameBy nn scope
  substNameBy nn $ ICase x y ty xs                 = ICase x (substNameBy nn y) (substNameBy nn ty) (substClause nn <$> xs)
  substNameBy nn $ ILocal x xs y                   = ?mapName_rhs_6 -- update local name too, if equal
  substNameBy nn $ IUpdate x xs y                  = ?mapName_rhs_7
  substNameBy nn $ IApp x y z                      = IApp x (substNameBy nn y) (substNameBy nn z)
  substNameBy nn $ INamedApp x y z w               = INamedApp x (substNameBy nn y) z (substNameBy nn w)
  substNameBy nn $ IAutoApp x y z                  = IAutoApp x (substNameBy nn y) (substNameBy nn z)
  substNameBy nn $ IWithApp x y z                  = IWithApp x (substNameBy nn y) (substNameBy nn z)
  substNameBy nn $ x@(ISearch _ _)                 = x
  substNameBy nn $ IAlternative x y xs             = ?mapName_rhs_13
  substNameBy nn $ IRewrite x y z                  = IRewrite x (substNameBy nn y) (substNameBy nn z)
  substNameBy nn $ IBindHere x y z                 = ?mapName_rhs_15
  substNameBy nn $ IBindVar x y                    = ?mapName_rhs_16
  substNameBy nn $ IAs x nameFC y z w              = ?mapName_rhs_17
  substNameBy nn $ IMustUnify x y z                = ?mapName_rhs_18
  substNameBy nn $ IDelayed x y z                  = IDelayed x y (substNameBy nn z)
  substNameBy nn $ IDelay x y                      = IDelay x (substNameBy nn y)
  substNameBy nn $ IForce x y                      = IForce x (substNameBy nn y)
  substNameBy nn $ x@(IQuote _ _)                  = x
  substNameBy nn $ x@(IQuoteName _ _)              = x
  substNameBy nn $ x@(IQuoteDecl _ _)              = x
  substNameBy nn $ IUnquote x y                    = IUnquote x (substNameBy nn y)
  substNameBy nn $ x@(IPrimVal _ _)                = x
  substNameBy nn $ x@(IType _)                     = x
  substNameBy nn $ x@(IHole _ _)                   = x
  substNameBy nn $ x@(Implicit _ _)                = x
  substNameBy nn $ IWithUnambigNames x xs y        = ?mapName_rhs_30
