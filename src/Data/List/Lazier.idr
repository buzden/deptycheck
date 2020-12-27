module Data.List.Lazier

import Data.Fin
import Data.List
import Data.List.Lazy
import Data.Nat

import Decidable.Equality

%default total

data LzVect : Nat -> Type -> Type

||| List with lazy contents and statically known size.
public export
record LzList a where
  constructor MkLzList
  length   : Nat
  contents : Lazy (LzVect length a)

%name LzList xs, ys, zs

export
data LzVect : Nat -> Type -> Type where
  Eager  : (xs : List a) -> LzVect (length xs) a
  Replic : (count : Nat) -> a -> LzVect count a
  Map    : (a -> b) -> (xs : LzList a) -> LzVect xs.length b
  Concat : (ls : LzList a) -> (rs : LzList a) -> LzVect (ls.length + rs.length) a
  Cart   : (os : LzList a) -> (is : LzList b) -> LzVect (os.length * is.length) (a, b)

%name LzVect lvxs, lvys, lvzs

--- Common functions ---

export
fromList : List a -> LzList a
fromList xs = MkLzList _ $ Eager xs

export
Nil : LzList a
Nil = fromList []

lzNull : LzList a -> Bool
lzNull xs = xs.length == 0

export
(++) : LzList a -> LzList a -> LzList a
xs ++ ys = if lzNull xs then ys else
           if lzNull ys then xs else
             MkLzList _ $ Concat xs ys

export
replicate : Nat -> a -> LzList a
replicate Z _ = []
replicate n x = MkLzList _ $ Replic n x

namespace FinFun

  export
  finToNatWeakenNNeutral : (k : Nat) -> (a : Fin n) -> finToNat (weakenN k a) = finToNat a
  finToNatWeakenNNeutral k FZ     = Refl
  finToNatWeakenNNeutral k (FS x) = rewrite finToNatWeakenNNeutral k x in Refl

  export
  finToNatShift : (k : Nat) -> (a : Fin n) -> finToNat (shift k a) = k + finToNat a
  finToNatShift Z     a = Refl
  finToNatShift (S k) a = rewrite finToNatShift k a in Refl

  ---------

  export
  splitSumFin : {a : Nat} -> Fin (a + b) -> Either (Fin a) (Fin b)
  splitSumFin {a=Z}   x      = Right x
  splitSumFin {a=S k} FZ     = Left FZ
  splitSumFin {a=S k} (FS x) = bimap FS id $ splitSumFin x

  export
  0 splitSumFin_correctness : {a, b : Nat} -> (x : Fin $ a + b) ->
                              case splitSumFin {a} {b} x of
                                Left  l => x = weakenN b l
                                Right r => x = shift a r
  splitSumFin_correctness {a=Z}   x  = Refl
  splitSumFin_correctness {a=S k} FZ = Refl
  splitSumFin_correctness {a=S k} (FS x) with (splitSumFin_correctness x)
    splitSumFin_correctness {a=S k} (FS x) | subcorr with (splitSumFin x)
      splitSumFin_correctness {a=S k} (FS x) | subcorr | Left  y = rewrite subcorr in Refl
      splitSumFin_correctness {a=S k} (FS x) | subcorr | Right y = rewrite subcorr in Refl

  export
  splitProdFin : {a, b : Nat} -> Fin (a * b) -> (Fin a, Fin b)
  splitProdFin {a=S _} x = case splitSumFin x of
    Left  y => (FZ, y)
    Right y => bimap FS id $ splitProdFin y

  export
  0 splitProdFin_correctness : {a, b : Nat} -> (x : Fin $ a * b) ->
                               let (o, i) = splitProdFin {a} {b} x in
                               finToNat x = finToNat o * b + finToNat i
  splitProdFin_correctness {a=S _} x with (splitSumFin_correctness x)
    splitProdFin_correctness x | sumcorr with (splitSumFin x)
      splitProdFin_correctness x | sumcorr | Left  y = rewrite sumcorr in finToNatWeakenNNeutral _ _
      splitProdFin_correctness x | sumcorr | Right y with (splitProdFin_correctness y)
        splitProdFin_correctness x | sumcorr | Right y | subcorr with (splitProdFin y)
          splitProdFin_correctness x | sumcorr | Right y | subcorr | (o, i) =
            rewrite sumcorr in
            rewrite finToNatShift b y in
            rewrite subcorr in
            rewrite plusAssociative b (finToNat o * b) (finToNat i) in
            Refl

export
index : (lz : LzList a) -> Fin lz.length -> a
index $ MkLzList {contents=Delay lv, _} = ind lv where
  ind : forall a. LzVect n a -> Fin n -> a
  ind (Eager xs)     i = index' xs i
  ind (Replic _ x)   _ = x
  ind (Map f xs)     i = f $ index xs i
  ind (Concat ls rs) i = either (index ls) (index rs) $ splitSumFin i
  ind (Cart os is)   i = bimap (index os) (index is) $ splitProdFin i

-------------------------------------------------
--- Funny implementations of funny interfaces ---
-------------------------------------------------

--- Monoid ---

Semigroup (LzList a) where
  (<+>) = (++)

Monoid (LzList a) where
  neutral = []

--- Folding ---

export
Foldable LzList where
  null = lzNull
  foldr f n $ MkLzList {contents=Delay lv, _} = case lv of
    Eager xs     => foldr f n xs
    Replic c x   => foldr f n $ Lazy.replicate c x
    Map g xs     => foldr (f . g) n xs
    Concat ls rs => foldr f (foldr f n rs) ls
    Cart os is   => foldr (\a, acc => foldr (f . (a, )) acc is) n os

--- Functor ---

export
Functor LzList where
  map f xs = MkLzList _ $ Map f xs
  -- TODO to think about map-fusion.

--- Folding (continued) ---

export
concatMap : Monoid m => (a -> m) -> LzList a -> m
concatMap mf lz@(MkLzList {contents=Delay lv, _}) = case lv of
  Eager xs     => concatMap mf xs
  Replic n x   => concatMap mf $ Lazy.replicate n x
  Map f xs     => Lazier.concatMap (mf . f) xs
  Concat ls rs => Lazier.concatMap mf ls <+> Lazier.concatMap mf rs
  Cart os is   => Lazier.concatMap mf $ assert_smaller lz $ Lazier.concatMap (\e => map (e, ) is) os

export
concat : Monoid a => LzList a -> a
concat = Lazier.concatMap id

--- Applicative-related ---

||| Produces a list which is a cartesian product of given lists with applied function to each element.
||| The resulting length is different with potential `zipWith` function despite the similarly looking signature.
export
cartWith : (f : a -> b -> c) -> LzList a -> LzList b -> LzList c
cartWith f xs ys = map (uncurry f) $ MkLzList _ $ Cart xs ys

0 cartWith_length_correct : (xs : LzList a) -> (ys : LzList b) -> (f : a -> b -> c) -> (cartWith f xs ys).length = xs.length * ys.length

export
Applicative LzList where
  pure x = fromList [x]
  (<*>) = cartWith apply

export
Alternative LzList where
  empty = []
  (<|>) = (++)

--- Cons function for lists syntax ---

export
(::) : a -> LzList a -> LzList a
x :: ll@(MkLzList {contents=Delay lv, _}) = case lv of
  Eager xs => fromList $ x::xs
  _        => pure x ++ ll

--- Splitting ---

export
uncons : LzList a -> Maybe (a, LzList a)
uncons $ MkLzList {contents = Delay lv, _} = unc lv where
  unc : forall a. LzVect n a -> Maybe (a, LzList a)
  unc $ Eager []      = Nothing
  unc $ Eager (x::xs) = Just (x, fromList xs)
  unc $ Replic Z x    = Nothing
  unc $ Replic (S n) x = Just (x, replicate n x)
  unc $ Map f xs      = bimap f (map f) <$> uncons xs
  unc $ Concat ls rs  = map (map (++ rs)) (uncons ls) <|> uncons rs
  unc $ Cart os is    = [| recart (uncons os) (uncons is) |] where
    recart : forall a, b. (a, LzList a) -> (b, LzList b) -> ((a, b), LzList (a, b))
    recart (x, xs) (y, ys) = ((x, y), map (, y) xs ++ [| (xs, ys) |])

0 uncons_length_correct : (lz : LzList a) -> case uncons lz of Nothing => Unit; Just (hd, tl) => lz.length = S tl.length

export
splitAt : (lz : LzList a) -> Fin lz.length -> (LzList a, LzList a)
splitAt (MkLzList {contents=Delay lv, _}) i = case lv of
  Eager xs     => let (l, r) = splitAt (finToNat i) xs in (fromList l, fromList r)
  Replic n x   => (replicate (finToNat i) x, replicate (n `minus` finToNat i) x)
  Map f xs     => let (l, r) = splitAt xs i in (map f l, map f r)
  Concat ls rs => case splitSumFin i of
                    Left  l => let (ll, rr) = splitAt ls l in (ll, rr ++ rs)
                    Right r => let (ll, rr) = splitAt rs r in (ls ++ ll, rs)
  Cart os is   => let (oi, ii) = splitProdFin i
                      (ibef, iaft) = splitAt is ii
                      topSq = MkLzList _ $ Cart os ibef
                  in case uncons iaft of
                    Nothing => (topSq, []) -- Actually, impossible case since the second element (i.e. `iaft`) cannot be empty
                    Just (p, ibot) => let (middleBef, middleAft) = splitAt (map (, p) os) oi
                                          botSq = MkLzList _ $ Cart os ibot
                                      in (topSq ++ middleBef, middleAft ++ botSq)

export
splitAt' : (lz : LzList a) -> Fin (S lz.length) -> (LzList a, LzList a)
splitAt' lz i = case strengthen i of
  Left _ => (lz, [])
  Right x => splitAt lz x

--- Conversions ---

export
toLazyList : LzList a -> LazyList a
toLazyList xs = assert_total $ unfoldr uncons xs -- total because uncons produces shorter list

--- Traversable ---

export
Traversable LzList where
  traverse f ll@(MkLzList {contents=Delay lv, _}) = case lv of
    Eager xs     => fromList <$> traverse f xs
    Replic n x   => replicate n <$> f x
    Map g xs     => traverse (f . g) xs
    Concat ls rs => [| traverse f ls ++ traverse f rs |]
    Cart _ _     => foldr (\curr, rest => [| f curr :: rest |]) (pure []) ll
                    -- This particular case is rather inffective. It loses the original lazy structure.
                    -- I don't know how to do better when we don't have `Monad LzList`.

--- Filtering ---

export
mapMaybe : (f : a -> Maybe b) -> LzList a -> LzList b
mapMaybe f ll@(MkLzList {contents=Delay lz, _}) = case lz of
  Eager xs     => fromList $ mapMaybe f xs
  Replic Z _   => []
  Replic n x   => maybe [] (replicate n) $ f x
  Map g xs     => mapMaybe (f . g) xs
  Concat ls rs => mapMaybe f ls ++ mapMaybe f rs
  Cart os is   => foldr (fo . f) [] ll where -- This does not preverse the shape in the general case.
    fo : Maybe b -> LzList b -> LzList b
    fo mb tl = maybe tl (::tl) mb

--- Show ---

export
Show a => Show (LzList a) where
  show = show . toList
