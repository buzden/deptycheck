module Data.List.CheckedEmpty

import Data.Bool
import Data.List1
import Data.Vect

%default total

public export
data CEList : (nonEmpty : Bool) -> Type -> Type where
  Nil  : CEList False a
  (::) : a -> CEList e a -> CEList True a

%name CEList xs, ys, zs

public export %inline
NEList : Type -> Type
NEList = CEList True

--- Basic functions ---

public export
length : CEList ne a -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export
(++) : (l : CEList nel a) -> (r : CEList ner a) -> CEList (nel || ner) a
[]      ++ ys = ys
(x::xs) ++ ys = x :: xs ++ ys

--- Functor ---

export
Functor (CEList ne) where
  map f []      = []
  map f (x::xs) = f x :: map f xs

export
pure : a -> NEList a
pure x = [x]

export
(>>=) : CEList nel a -> (a -> CEList ner b) -> CEList (nel && ner) b
(>>=) [] _ = []
(>>=) ((::) x xs {e=nem}) f = do
  rewrite sym $ orSameAndRightNeutral ner nem
  rewrite andCommutative ner nem
  f x ++ (xs >>= f)

export
(<*>) : CEList nel (a -> b) -> CEList ner a -> CEList (nel && ner) b
xs <*> ys = xs >>= (<$> ys)

--- Folds ---

export
Foldable (CEList ne) where
  foldr c n []      = n
  foldr c n (x::xs) = c x (foldr c n xs)

  foldl f q []      = q
  foldl f q (x::xs) = foldl f (f q x) xs

  null []     = True
  null (_::_) = False

  toList []      = []
  toList (x::xs) = x :: toList xs

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral

export
foldl1 : (a -> a -> a) -> NEList a -> a
foldl1 f (x::xs) = foldl f x xs

export
foldr1 : (a -> a -> a) -> NEList a -> a
foldr1 f (x::xs) = foldr f x xs

export
Traversable (CEList ne) where
  traverse f []      = pure []
  traverse f (x::xs) = [| f x :: traverse f xs |]

--- Conversions ---

-- List --

public export
fromList : (xs : List a) -> CEList (not $ null xs) a
fromList []      = []
fromList (x::xs) = x :: fromList xs

-- List1 --

public export
fromList1 : List1 a -> NEList a
fromList1 $ x:::xs = x :: fromList xs

public export
toList1 : NEList a -> List1 a
toList1 $ x::xs = x ::: toList xs

-- Vect --

public export
fromVect : Vect n a -> CEList (n /= Z) a
fromVect []      = []
fromVect (x::xs) = x :: fromVect xs

--- Showing ---

export
Show a => Show (CEList ne a) where
  show = show . toList

--- Properties ---

export
mapFusion : (g : b -> c) -> (f : a -> b) -> (xs : CEList ne a) -> map g (map f xs) = map (g . f) xs
mapFusion g f []      = Refl
mapFusion g f (x::xs) = rewrite mapFusion g f xs in Refl

export
mapExt : (xs : CEList ne _) -> ((x : _) -> f x = g x) -> map f xs = map g xs
mapExt []      _  = Refl
mapExt (x::xs) fg = rewrite fg x in cong (g x ::) $ mapExt _ fg
