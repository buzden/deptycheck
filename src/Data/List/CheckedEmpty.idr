module Data.List.CheckedEmpty

import Data.Bool
import Data.List1
import Data.Vect

%default total

--- Some magic for providing a default choice ---

export
interface DefaultChoiceMagic (0 a : Bool) where
  constructor MkDefaultChoiceMagic

export %defaulthint
0 DDefaultChoiceMagic : DefaultChoiceMagic True
DDefaultChoiceMagic = MkDefaultChoiceMagic

export
DefaultChoiceMagic b where

--- Types definitions ---

public export
data CEList : (definitelyNotEmpty : Bool) -> Type -> Type where
  Nil  : CEList False a
  (::) : (0 _ : DefaultChoiceMagic e) => a -> CEList e a -> CEList ne a

%name CEList xs, ys, zs

public export %inline
NEList : Type -> Type
NEList = CEList True

--- Examples ---

0 e_f_0 : CEList False Nat
e_f_0 = []

0 e_f_2 : CEList False Nat
e_f_2 = [1, 2]

0 e_f_5 : CEList False Nat
e_f_5 = [1, 2, 3, 4, 5]

0 e_f_a : CEList False Nat
e_f_a = 0 :: e_f_5

failing

  0 e_t_0 : CEList True Nat
  e_t_0 = []

0 e_t_2 : CEList True Nat
e_t_2 = [1, 2]

0 e_t_5 : CEList True Nat
e_t_5 = [1, 2, 3, 4, 5]

0 e_t_a : CEList True Nat
e_t_a = 0 :: e_t_5

--- Basic functions ---

public export
length : CEList ne a -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export
(++) : (l : CEList nel a) -> (r : CEList ner a) -> CEList (nel || ner) a
[]      ++ ys = ys
(x::xs) ++ ys = x :: xs ++ ys

--- Internal conversions ---

-- Relaxation --

public export
relaxF : CEList ne a -> CEList False a
relaxF []      = []
relaxF (x::xs) = x::xs

public export
relaxT : NEList a -> CEList ne a
relaxT (x::xs) = x::xs

public export
relaxAnd : CEList ne a -> CEList (ne && nx) a
relaxAnd [] = []
relaxAnd (x::xs) = x::xs

--public export
--relaxOr : CEList (ne || nx) a -> CEList ne a
--relaxOr [] = []
--relaxOr (x::xs) = x::xs

-- Strengthening --

public export
toNEList : CEList ne a -> Maybe $ NEList a
toNEList []      = Nothing
toNEList (x::xs) = Just $ x::xs

--- Functor ---

export
Functor (CEList ne) where
  map f []      = []
  map f (x::xs) = f x :: map f xs

export
pure : a -> CEList ne a
pure x = [x]

export
(>>=) : CEList nel a -> (a -> CEList ner b) -> CEList (nel && ner) b
(>>=) [] _ = []
(>>=) wh@(x::xs) f = do
  rewrite andCommutative nel ner
  let Just nxs = toNEList xs
    | Nothing => relaxAnd $ f x
  rewrite sym $ orSameNeutral ner
  relaxAnd $ f x ++ (assert_smaller wh nxs >>= f)

export
(>>) : CEList nel a -> CEList ner b -> CEList (nel && ner) b
(>>) xs ys = xs >>= \_ => ys

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

--- Filtering ---

export
filter : (a -> Bool) -> CEList ne a -> CEList False a
filter _ []      = []
filter f (x::xs) = if f x then x :: filter f xs else filter f xs

export
mapMaybe : (a -> Maybe b) -> CEList ne a -> CEList False b
mapMaybe _ [] = []
mapMaybe f (x::xs) = case f x of
                       Just y  => y :: mapMaybe f xs
                       Nothing => mapMaybe f xs

--- External conversions ---

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
