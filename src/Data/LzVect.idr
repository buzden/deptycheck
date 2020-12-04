module Data.LzVect

import Data.Fin
import Data.List

import Decidable.Equality

%default total

public export
data LzVect : Nat -> Type -> Type where
  Nil  : LzVect Z a
  (::) : a -> Lazy (LzVect n a) -> LzVect (S n) a
  (++) : {n, m : Nat} -> Lazy (LzVect n a) -> Lazy (LzVect m a) -> LzVect (n + m) a

%name LzVect xs, ys, zs

public export
LzVect_N : Type -> Type
LzVect_N a = (n ** LzVect n a)

%name LzVect_N n_xs, n_ys, n_zs

--- Common functions ---

public export
length : LzVect n a -> Nat
length [] = Z
length (_::xs) = S $ length xs
length ((++) _ _ {n} {m}) = n + m

export
lengthCorrect : (xs : LzVect n a) -> length xs = n
lengthCorrect [] = Refl
lengthCorrect (x::xs) = rewrite lengthCorrect xs in Refl
lengthCorrect (xs ++ ys) = Refl

public export
index : (v : LzVect n a) -> Fin n -> a
index (x::_)  FZ     = x
index (_::xs) (FS i) = index xs i
index (xs ++ ys) i   = ?index_rhs_3

public export
replicate : (n : Nat) -> a -> LzVect n a
replicate Z     _ = []
replicate (S n) x = x :: replicate n x

-------------------------------------------------
--- Funny implementations of funny interfaces ---
-------------------------------------------------

--- Equalities ---

Eq a => Eq (LzVect n a) where
  (==) = ?eq_rhs

DecEq a => DecEq (LzVect n a) where
  decEq = ?decEq_rhs

--- Order ---

Ord a => Ord (LzVect n a) where
  compare = ?compare_rhs

--- Functor-related ---

Functor (LzVect n) where
  map = ?map_rhs

Functor LzVect_N where
  map f (n ** lv) = (n ** map f lv)

mapMaybe : (f : a -> Maybe b) -> LzVect n a -> LzVect_N a

zipWith : (f : a -> b -> c) -> LzVect n a -> LzVect n b -> LzVect n c

{n : Nat} -> Applicative (LzVect n) where
  pure = replicate _
  (<*>) = zipWith apply

Applicative LzVect_N where
  pure x = (1 ** [x])
  (n ** xs) <*> (m ** ys) = ?ap_n_rhs

(>>=) : LzVect n a -> (a -> LzVect_N a) -> LzVect_N a
(>>=) = ?bind_rhs

Monad LzVect_N where
  (>>=) = ?bind_n_rhs

--- Folds ---

Foldable (LzVect n) where
  foldr = ?foldr_rhs

Traversable (LzVect n) where
  traverse = ?traverse_rhs

--- Show ---

Show a => Show (LzVect n a) where
  show = show . toList
