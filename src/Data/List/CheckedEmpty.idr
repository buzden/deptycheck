module Data.List.CheckedEmpty

import Data.Bool
import Data.List1
import Data.Vect

%default total

public export
data NEList : (nonEmpty : Bool) -> Type -> Type where
  Nil  : NEList False a
  (::) : a -> NEList e a -> NEList True a

%name NEList xs, ys, zs

--- Basic functions ---

public export
length : NEList ne a -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export
(++) : (l : NEList nel a) -> (r : NEList ner a) -> NEList (nel || ner) a
[]      ++ ys = ys
(x::xs) ++ ys = x :: xs ++ ys

--- Functor ---

export
Functor (NEList ne) where
  map f []      = []
  map f (x::xs) = f x :: map f xs

export
pure : a -> NEList True a
pure x = [x]

export
(>>=) : NEList nel a -> (a -> NEList ner b) -> NEList (nel && ner) b
(>>=) [] _ = []
(>>=) ((::) x xs {e=nem}) f = do
  rewrite sym $ orSameAndRightNeutral ner nem
  rewrite andCommutative ner nem
  f x ++ (xs >>= f)

export
(<*>) : NEList nel (a -> b) -> NEList ner a -> NEList (nel && ner) b
xs <*> ys = xs >>= (<$> ys)

--- Folds ---

export
Foldable (NEList ne) where
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
foldl1 : (a -> a -> a) -> NEList True a -> a
foldl1 f (x::xs) = foldl f x xs

export
foldr1 : (a -> a -> a) -> NEList True a -> a
foldr1 f (x::xs) = foldr f x xs

export
Traversable (NEList ne) where
  traverse f []      = pure []
  traverse f (x::xs) = [| f x :: traverse f xs |]

--- Conversions ---

-- List --

public export
fromList : (xs : List a) -> NEList (not $ null xs) a
fromList []      = []
fromList (x::xs) = x :: fromList xs

-- List1 --

public export
fromList1 : List1 a -> NEList True a
fromList1 $ x:::xs = x :: fromList xs

public export
toList1 : NEList True a -> List1 a
toList1 $ x::xs = x ::: toList xs

-- Vect --

public export
fromVect : Vect n a -> NEList (n /= Z) a
fromVect []      = []
fromVect (x::xs) = x :: fromVect xs

--- Showing ---

export
Show a => Show (NEList ne a) where
  show = show . toList
