module Data.Vect.Dependent

import Data.Fin
import Data.Vect

%default total

public export
data DVect : (n : Nat) -> (Fin n -> Type) -> Type where
  Nil  : DVect Z ty
  (::) : (a : ty FZ) -> DVect n (ty . FS) -> DVect (S n) ty

%name Dependent.DVect xs, ys, zs

--- Indexing ---

public export
index : (i : Fin n) -> DVect n a -> a i
index FZ     (x::_ ) = x
index (FS i) (_::xs) = index i xs

--- Creation ---

public export
tabulate : {n : Nat} -> {0 a : Fin n -> Type} -> ((i : Fin n) -> a i) -> DVect n a
tabulate {n=Z}   _ = []
tabulate {n=S n} f = f FZ :: tabulate (\i => f $ FS i)

--- Changes ---

public export
replaceAt : (i : Fin n) -> a i -> DVect n a -> DVect n a
replaceAt FZ     w (_::xs) = w :: xs
replaceAt (FS i) w (x::xs) = x :: replaceAt i w xs

public export
updateAt : (i : Fin n) -> (a i -> a i) -> DVect n a -> DVect n a
updateAt FZ     f (x::xs) = f x :: xs
updateAt (FS i) f (x::xs) = x :: updateAt i f xs

--- Mappings ---

public export
map : ((i : Fin n) -> a i -> b i) -> DVect n a -> DVect n b
map f []      = []
map f (x::xs) = f FZ x :: map (\i => f $ FS i) xs

public export %inline
(<$>) : ({i : Fin n} -> a i -> b i) -> DVect n a -> DVect n b
(<$>) = map

public export %inline
(<&>) : DVect n a -> ({i : Fin n} -> a i -> b i) -> DVect n b
(<&>) = flip map

--- Conversions ---

public export
downmap : ((i : Fin n) -> a i -> b) -> DVect n a -> Vect n b
downmap f []      = []
downmap f (x::xs) = f FZ x :: downmap (\i => f $ FS i) xs

public export
upmap : ((i : Fin n) -> a -> b i) -> Vect n a -> DVect n b
upmap f []      = []
upmap f (x::xs) = f FZ x :: upmap (\i => f $ FS i) xs

--- Zippings ---

public export
zip : DVect n a -> DVect n b -> DVect n $ \i => (a i, b i)
zip []      []      = []
zip (x::xs) (y::ys) = (x, y) :: zip xs ys

public export
zipWith : ((i : Fin n) -> a i -> b i -> c i) -> DVect n a -> DVect n b -> DVect n c
zipWith _ []      []      = []
zipWith f (x::xs) (y::ys) = f FZ x y :: zipWith (\i => f $ FS i) xs ys

public export
(<*>) : DVect n (\i => a i -> b i) -> DVect n a -> DVect n b
(<*>) []      []      = []
(<*>) (f::fs) (y::ys) = f y :: (fs <*> ys)

--- Restructuring ---

public export
transpose : {m : _} -> {0 a : Fin n -> Fin m -> Type} -> DVect n (\i => DVect m $ \j => a i j) -> DVect m (\j => DVect n $ \i => a i j)
transpose []      = tabulate $ \_ => []
transpose (x::xs) = zipWith (\_ => (::)) x $ transpose xs

--- Foldings ---

public export
foldl : ((i : Fin n) -> acc -> a i -> acc) -> acc -> DVect n a -> acc
foldl _ init [] = init
foldl f init (x::xs) = foldl (\i => f $ FS i) (f FZ init x) xs

public export
foldr : ((i : Fin n) -> a i -> Lazy acc -> acc) -> acc -> DVect n a -> acc
foldr _ init []      = init
foldr f init (x::xs) = f FZ x $ foldr (\i => f $ FS i) init xs

--- Traversals ---

public export
traverse : Applicative f => ((i : Fin n) -> a i -> f (b i)) -> DVect n a -> f (DVect n b)
traverse f []      = pure []
traverse f (x::xs) = [| f FZ x :: traverse (\i => f $ FS i) xs |]

public export %inline
for : Applicative f => DVect n a -> ((i : Fin n) -> a i -> f (b i)) -> f (DVect n b)
for = flip traverse
