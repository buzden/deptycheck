module Test.DepTyCheck.Gen

import Control.Monad.State

import Data.DPair
import Data.List
import Data.List.Lazier
import Data.List.Lazy
import Data.Stream
import Data.Vect

import Decidable.Equality

import public System.Random.Simple

%default total

---------------------------------------------
--- General decisions and magic constants ---
---------------------------------------------

-- All of those can (and even should) be generalized some day.

public export %inline
Seed : Type
Seed = StdGen

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

export
data Gen' : (carrier : Type -> Type) -> Type -> Type where
  Uniform : cr a -> Gen' cr a
  AlternG : cr (Gen' cr a) -> Gen' cr a
  Raw     : StateT Seed cr a -> Gen' cr a

public export
Gen : Type -> Type
Gen = Gen' ?whatever_carrier

-- TODO To think about arbitrary discrete final probability distribution instead of only uniform.

export
chooseAny : Random a => Applicative cr => Gen' cr a
chooseAny = Raw $ mapStateT (pure . runIdentity) random'

export
choose : Random a => Applicative cr => (a, a) -> Gen' cr a
choose = Raw . mapStateT (pure . runIdentity) . randomR'

export
unGen' : Monad cr => Gen' cr a -> StateT Seed cr a
unGen' (Raw sf)     = sf
unGen' (Uniform xs) = ?runCR xs
unGen' (AlternG gs) = lift gs >>= unGen'

export
Functor cr => Functor (Gen' cr) where
  map f (Uniform xs) = Uniform $ map f xs
  map f (AlternG gs) = AlternG $ assert_total $ map f <$> gs
  map f (Raw gena)   = Raw $ map f gena

apAsRaw : Monad cr => Gen' cr (a -> b) -> Gen' cr a -> Gen' cr b
apAsRaw generalF generalA = Raw $ unGen' generalF <*> unGen' generalA

export
Monad cr => Applicative (Gen' cr) where
  pure x = Uniform $ pure x

  Uniform fs <*> Uniform xs = Uniform $ fs <*> xs

  Uniform fs <*> AlternG gs = AlternG [| map fs gs |]
  AlternG gs <*> Uniform xs = AlternG [| (\gab, a => flip apply a <$> gab) gs xs |]
  AlternG fs <*> AlternG gs = AlternG $ assert_total [| fs <*> gs |]

  rawF@(Raw {}) <*> generalA = apAsRaw rawF generalA
  generalF <*> rawA@(Raw {}) = apAsRaw generalF rawA

export
Alternative cr => Monad cr => Alternative (Gen' cr) where
  empty = Uniform empty
  AlternG ls <|> Delay (AlternG rs) = AlternG $ ls <|> rs
  AlternG ls <|> Delay (generalR  ) = AlternG $ ls <|> pure generalR
  generalL   <|> Delay (AlternG rs) = AlternG $ pure generalL <|> rs
  generalL   <|> Delay (generalR  ) = AlternG $ pure generalL <|> pure generalR

||| Makes the given `Gen` to act as an independent generator according to the `Alternative` combination.
||| That is, in `independent (independent a <|> independent b)` given `a` and `b` are distributed evenly.
export
independent : Applicative cr => Gen' cr a -> Gen' cr a
independent alt@(AlternG _) = AlternG $ pure alt
independent other = other

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [a <|> b, c]` is not the same as `a <|> b <|> c`.
||| In this example case, generator `a <|> b` and generator `c` will have the same probability in the resulting generator,
||| i.e., `oneOf [a <|> b, c]` is equivalent to `independent (a <|> b) <|> independent c`.
|||
||| If you want generators in the list to be treated non-independent, you can use the `choice` function from prelude.
|||
||| The resulting generator is not independent, i.e. `oneOf [a, b, c] <|> oneOf [d, e]` is equivalent to `oneOf [a, b, c, d, e]`.
public export
oneOf : Alternative cr => Monad cr => List (Gen' cr a) -> Gen' cr a
oneOf []      = empty
oneOf [x]     = independent x
oneOf (x::xs) = independent x <|> oneOf xs

replicate : Alternative f => Nat -> a -> f a
replicate 0     _ = empty
replicate 1     x = pure x
replicate (S n) x = pure x <|> replicate n x

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
|||
||| The resulting generator is not independent, i.e. `frequency [(n1, g1), (n2, g2)] <|> frequency [(n3, g3), (n4, g4)]` is
||| equivalent to `frequency [(n1, g1), (n2, g2), (n3, g3), (n4, g4)]`.
||| Also, `frequency [(n, g), (m, h)] <|> oneOf [u, w]` is equivalent to `frequency [(n, g), (m, h), (1, u), (1, w)]`.
export
frequency : Alternative cr => Monad cr => List (Nat, Gen' cr a) -> Gen' cr a
frequency = AlternG . concatMap @{MonoidAlternative} (uncurry replicate . map independent)

||| Choose one of the given generators with probability proportional to the given value, treating all source generators dependently.
|||
||| This function is similar to `frequency` but as of it takes internal alternative combinations inside the given generators level up.
||| That is, unlike the `frequency` function, `frequency' [(n, oneOf [a, b, c]), (m, x)]` is equivalent to
||| `frequency [(n, a), (n, b), (n, c), (m, x)]`
export
frequency_dep : Alternative cr => Monad cr => List (Nat, Gen' cr a) -> Gen' cr a
frequency_dep = AlternG . concatMap @{MonoidAlternative} (uncurry replicate)

fromFoldable : Alternative t => Foldable f => f a -> t a
fromFoldable = concatMap @{MonoidAlternative} pure

||| Choose one of the given values uniformly.
|||
||| The resulting generator is not independent, i.e. `elements xs <|> elements ys` is equivalent to `elements (xs ++ ys)`.
export
elements : Alternative cr => Monad cr => List a -> Gen' cr a
elements = Uniform . fromFoldable

export
elements' : Foldable f => Alternative cr => Monad cr => f a -> Gen' cr a
elements' = Uniform . fromFoldable

export
Foldable cr => Alternative cr => Monad cr => Monad (Gen' cr) where
  Uniform gs >>= c = if null gs then Uniform empty else AlternG $ c <$> gs
  AlternG gs >>= c = AlternG $ assert_total (>>= c) <$> gs
  Raw sf     >>= c = Raw $ sf >>= unGen' . c

export
mapMaybe : (a -> Maybe b) -> Gen' cr a -> Gen' cr b
--mapMaybe p (Uniform l) = Uniform $ mapMaybe p l
--mapMaybe p (AlternG l) = AlternG $ assert_total $ mapMaybe p <$> l
--mapMaybe p (Raw sf)    = Raw $ mapMaybe p <$> sf

export
suchThat_withPrf : Gen' cr a -> (p : a -> Bool) -> Gen' cr $ a `Subset` So . p
suchThat_withPrf g p = mapMaybe lp g where
  lp : a -> Maybe $ a `Subset` So . p
  lp x with (p x) proof prf
    lp x | True  = Just $ Element x $ eqToSo prf
    lp x | False = Nothing

infixl 4 `suchThat`

public export
suchThat : Functor cr => Gen' cr a -> (a -> Bool) -> Gen' cr a
suchThat g p = fst <$> suchThat_withPrf g p

export
suchThat_dec : Gen' cr a -> ((x : a) -> Dec (prop x)) -> Gen' cr $ Subset a prop
suchThat_dec g f = mapMaybe d g where
  d : a -> Maybe $ Subset a prop
  d x = case f x of
    Yes p => Just $ Element x p
    No  _ => Nothing

||| Filters the given generator so, that resulting values `x` are solutions of equation `y = f x` for given `f` and `y`.
export
suchThat_invertedEq : DecEq b => Gen' cr a -> (y : b) -> (f : a -> b) -> Gen' cr $ Subset a $ \x => y = f x
suchThat_invertedEq g y f = g `suchThat_dec` \x => y `decEq` f x

-- TODO to reimplement `variant` to ensure that variant of `Uniform` is left `Uniform`.
export
variant : Monad cr => Nat -> Gen' cr a -> Gen' cr a
variant Z       gen = gen
variant x@(S _) gen = Raw $ modify (index x . iterate (fst . next)) *> unGen' gen

export
listOf : Foldable cr => Alternative cr => Monad cr => {default (choose (0, 10)) length : Gen' cr Nat} -> Gen' cr a -> Gen' cr (List a)
listOf g = sequence $ List.replicate !length g

export
vectOf : Monad cr => {n : Nat} -> Gen' cr a -> Gen' cr (Vect n a)
vectOf g = sequence $ replicate n g
