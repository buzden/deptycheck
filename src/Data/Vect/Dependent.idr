module Data.Vect.Dependent

import Data.Either
import Data.Fin
import Data.Fin.Extra
import Data.Vect

-- TODO to refactor utils to not to have dependency to `Deriving.*` packages from here
import Deriving.DepTyCheck.Util.Fin

%default total

public export
data DVect : (n : Nat) -> (Fin n -> Type) -> Type where
  Nil  : DVect Z ty
  (::) : (a : ty FZ) -> DVect n (ty . FS) -> DVect (S n) ty

%name DVect xs, ys, zs

--- Indexing ---

public export
index : (i : Fin n) -> DVect n a -> a i
index FZ     (x::_ ) = x
index (FS i) (_::xs) = index i xs

--- Creation ---

public export
tabulateI : {n : Nat} -> {0 a : Fin n -> Type} -> ((i : Fin n) -> a i) -> DVect n a
tabulateI {n=Z}   _ = []
tabulateI {n=S n} f = f FZ :: tabulateI (\i => f $ FS i)

public export %inline
tabulate : {n : Nat} -> {0 a : Fin n -> Type} -> ({i : Fin n} -> a i) -> DVect n a
tabulate = tabulateI

--- Concating ---

public export
(++) : DVect n a -> DVect m b -> DVect (n + m) $ either a b . Fin.Extra.splitSum
(++) []      ys = ys
(++) (x::xs) ys = x :: rewrite funext $ \x => eitherBimapFusion a b FS id $ splitSum x in (xs ++ ys) where
  0 funext : ((x : _) -> f x = g x) -> f = g
  funext _ = believe_me $ the (Z = Z) Refl

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
mapI : ((i : Fin n) -> a i -> b i) -> DVect n a -> DVect n b
mapI f []      = []
mapI f (x::xs) = f FZ x :: mapI (\i => f $ FS i) xs

public export %inline
map : ({i : Fin n} -> a i -> b i) -> DVect n a -> DVect n b
map = mapI

public export %inline
(<$>) : ({i : Fin n} -> a i -> b i) -> DVect n a -> DVect n b
(<$>) = map

public export %inline
(<&>) : DVect n a -> ({i : Fin n} -> a i -> b i) -> DVect n b
(<&>) = flip map

public export
mapPreI : ((i : Fin n) -> DVect (finToNat i) (b . weakenToSuper {i}) -> a i -> b i) -> DVect n a -> DVect n b
mapPreI f []      = []
mapPreI f (x::xs) = let y = f FZ [] x in y :: mapPreI (\i, ys => f (FS i) (y::ys)) xs

public export %inline
mapPre : ({i : Fin n} -> DVect (finToNat i) (b . weakenToSuper {i}) -> a i -> b i) -> DVect n a -> DVect n b
mapPre = mapPreI

--- Conversions ---

public export
downmapI : ((i : Fin n) -> a i -> b) -> DVect n a -> Vect n b
downmapI f []      = []
downmapI f (x::xs) = f FZ x :: downmapI (\i => f $ FS i) xs

public export %inline
downmap : ({i : Fin n} -> a i -> b) -> DVect n a -> Vect n b
downmap = downmapI

public export
upmapI : ((i : Fin n) -> a -> b i) -> Vect n a -> DVect n b
upmapI f []      = []
upmapI f (x::xs) = f FZ x :: upmapI (\i => f $ FS i) xs

public export
upmap : ({i : Fin n} -> a -> b i) -> Vect n a -> DVect n b
upmap = upmapI

--- Zippings ---

public export
zip : DVect n a -> DVect n b -> DVect n $ \i => (a i, b i)
zip []      []      = []
zip (x::xs) (y::ys) = (x, y) :: zip xs ys

public export
zipWithI : ((i : Fin n) -> a i -> b i -> c i) -> DVect n a -> DVect n b -> DVect n c
zipWithI _ []      []      = []
zipWithI f (x::xs) (y::ys) = f FZ x y :: zipWithI (\i => f $ FS i) xs ys

public export %inline
zipWith : ({i : Fin n} -> a i -> b i -> c i) -> DVect n a -> DVect n b -> DVect n c
zipWith = zipWithI

public export
(<*>) : DVect n (\i => a i -> b i) -> DVect n a -> DVect n b
(<*>) []      []      = []
(<*>) (f::fs) (y::ys) = f y :: (fs <*> ys)

--- Restructuring ---

public export
transpose : {m : _} -> {0 a : Fin n -> Fin m -> Type} -> DVect n (\i => DVect m $ \j => a i j) -> DVect m (\j => DVect n $ \i => a i j)
transpose []      = tabulate []
transpose (x::xs) = zipWith (::) x $ transpose xs

--- Foldings ---

public export
foldlI : ((i : Fin n) -> acc -> a i -> acc) -> acc -> DVect n a -> acc
foldlI _ init [] = init
foldlI f init (x::xs) = foldlI (\i => f $ FS i) (f FZ init x) xs

public export %inline
foldl : ({i : Fin n} -> acc -> a i -> acc) -> acc -> DVect n a -> acc
foldl = foldlI

public export
foldrI : ((i : Fin n) -> a i -> Lazy acc -> acc) -> acc -> DVect n a -> acc
foldrI _ init []      = init
foldrI f init (x::xs) = f FZ x $ foldrI (\i => f $ FS i) init xs

public export %inline
foldr : ({i : Fin n} -> a i -> Lazy acc -> acc) -> acc -> DVect n a -> acc
foldr = foldrI

public export
foldlMI : Monad m => ((i : Fin n) -> acc -> a i -> m acc) -> acc -> DVect n a -> m acc
foldlMI fm = foldlI (\i, ma, b => ma >>= flip (fm i) b) . pure

public export
foldlM : Monad m => ({i : Fin n} -> acc -> a i -> m acc) -> acc -> DVect n a -> m acc
foldlM = foldlMI

--- Traversals ---

public export
traverseI : Applicative f => ((i : Fin n) -> a i -> f (b i)) -> DVect n a -> f (DVect n b)
traverseI f []      = pure []
traverseI f (x::xs) = [| f FZ x :: traverseI (\i => f $ FS i) xs |]

public export %inline
traverse : Applicative f => ({i : Fin n} -> a i -> f (b i)) -> DVect n a -> f (DVect n b)
traverse = traverseI

public export
sequence : Applicative f => DVect n (f . a) -> f (DVect n a)
sequence = traverse id

public export %inline
forI : Applicative f => DVect n a -> ((i : Fin n) -> a i -> f (b i)) -> f (DVect n b)
forI = flip traverseI

public export %inline
for : Applicative f => DVect n a -> ({i : Fin n} -> a i -> f (b i)) -> f (DVect n b)
for = flip traverse

--- Standard interfaces' implementations ---

public export
({i : Fin n} -> Eq (a i)) => Eq (DVect n a) where
  (==) = all id .: downmap id .: zipWith (==)

public export
({i : Fin n} -> Ord (a i)) => Ord (DVect n a) where
  compare = concat .: downmap id .: zipWith compare

public export
({i : Fin n} -> Show (a i)) => Show (DVect n a) where
  show = concat . ("[" ::) . (`snoc` "]") . intersperse ", " . downmap show
  -- if you do `show = show . downmap show`, all elements will be wrapped in odd `"`s because of `Show String` instance.

public export
({i : Fin n} -> Semigroup (a i)) => Semigroup (DVect n a) where
  (<+>) = zipWith (<+>)

public export
{n : Nat} -> {0 a : Fin n -> Type} ->
({i : Fin n} -> Monoid (a i)) => Monoid (DVect n a) where
  neutral = tabulate neutral
