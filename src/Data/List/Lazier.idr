module Data.List.Lazier

import Control.Monad.State
import Control.Monad.Error.Interface

import Data.Fin
import Data.Fin.Extra
import Data.List
import Data.List.Lazy
import Data.Nat

import Decidable.Equality

import System.Random.Simple

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
  Hide   : (xs : LzList a) -> LzVect 1 a

%name LzVect lvxs, lvys, lvzs

--- Common functions ---

export
fromList : List a -> LzList a
fromList xs = MkLzList _ $ Eager xs

export
fromFoldable : Foldable f => f a -> LzList a
fromFoldable = fromList . toList -- TODO maybe, to do this somehow better?

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

export
hideLength : LzList a -> LzList a
hideLength ll = if lzNull ll then [] else MkLzList _ $ Hide ll

-------------------------------------------------
--- Funny implementations of funny interfaces ---
-------------------------------------------------

--- Monoid ---

public export
Semigroup (LzList a) where
  (<+>) = (++)

public export
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
    Hide xs      => foldr f n xs

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
  Hide xs      => Lazier.concatMap mf xs

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

public export
Alternative LzList where
  empty = []
  a <|> b = a ++ b

export
Monad LzList where
  (>>=) = flip Lazier.concatMap

--- Cons function for lists syntax ---

export
(::) : a -> LzList a -> LzList a
x :: ll@(MkLzList {contents=Delay lv, _}) = case lv of
  Eager xs => fromList $ x::xs
  _        => pure x ++ ll

--- Splitting ---

export
uncons : LzList a -> Maybe (a, LzList a)
uncons $ MkLzList {contents = Delay lv, _} = case lv of
  Eager []       => Nothing
  Eager (x::xs)  => Just (x, fromList xs)
  Replic Z x     => Nothing
  Replic (S n) x => Just (x, replicate n x)
  Map f xs       => bimap f (map f) <$> uncons xs
  Concat ls rs   => map (map (++ rs)) (uncons ls) <|> uncons rs
  Hide xs        => uncons xs <&> mapSnd hideLength
  Cart os is     => [| recart (uncons os) (uncons is) |] where
    recart : forall a, b. (a, LzList a) -> (b, LzList b) -> ((a, b), LzList (a, b))
    recart (x, xs) (y, ys) = ((x, y), map (, y) xs ++ [| (xs, ys) |])

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
    Cart os is   => Lazier.concatMap @{MonoidApplicative} (\x => traverse (f . (x,)) is) os
    Hide xs      => traverse f xs <&> hideLength

--- Filtering ---

export
mapMaybe : (f : a -> Maybe b) -> LzList a -> LzList b
mapMaybe f ll@(MkLzList {contents=Delay lv, _}) = case lv of
  Eager xs     => fromList $ mapMaybe f xs
  Replic Z _   => []
  Replic n x   => maybe [] (replicate n) $ f x
  Map g xs     => mapMaybe (f . g) xs
  Concat ls rs => mapMaybe f ls ++ mapMaybe f rs
  Cart os is   => os >>= \x => mapMaybe (f . (x,)) is
  Hide xs      => hideLength $ mapMaybe f xs

--- Show ---

export
Show a => Show (LzList a) where
  show = show . toList

--- Random-related functions ---

randomFin : RandomGen g => MonadState g m => MonadError () m => {n : _} -> m $ Fin n
randomFin {n = Z}   = throwError ()
randomFin {n = S k} = random'

lrProportionally : RandomGen g => MonadState g m => MonadError () m => (l, r : Nat) -> m Bool
lrProportionally Z Z = throwError ()
lrProportionally l r = (< cast l) <$> randomR' {a=Int} (0, cast l + cast r - 1)
-- We do this through `Int`!

export
pickUniformly : RandomGen g => MonadState g m => MonadError () m => LzList a -> m a
pickUniformly ll@(MkLzList {contents=Delay lv, length}) = case lv of
  Eager xs     => index' xs <$> randomFin {n=length}
  Replic _ x   => pure x
  Map f xs     => f <$> pickUniformly xs
  Concat ls rs => lrProportionally ls.length rs.length >>= \lr => pickUniformly $ assert_smaller ll $ if lr then ls else rs
  Cart os is   => [| (pickUniformly os, pickUniformly is) |]
  Hide xs      => pickUniformly xs
