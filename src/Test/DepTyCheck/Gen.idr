module Test.DepTyCheck.Gen

import Control.Monad.Random
import public Control.Monad.Random.Interface
import Control.Monad.State
import public Control.Monad.State.Interface
import public Control.Monad.Error.Interface
import Control.Monad.Maybe

import Data.DPair
import Data.Nat.Pos
import Data.Fuel
import Data.List
import Data.CheckedEmpty.List.Lazy
import public Data.List.Lazy
import Data.Vect
import Data.Stream

import Decidable.Equality

import public Language.Implicits.IfUnsolved

import public System.Random.Pure

import Test.DepTyCheck.Gen.NonEmpty

%default total

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

export
data Gen : Type -> Type where
  [noHints]
  Empty    : Gen a
  NonEmpty : Lazy (Gen1 $ Maybe a) -> Gen a

-----------------------------
--- Very basic generators ---
-----------------------------

export
chooseAny : Random a => Gen a
chooseAny = NonEmpty $ Just <$> chooseAny

export
choose : Random a => (a, a) -> Gen a
choose bounds = NonEmpty $ Just <$> choose bounds

export
empty : Gen a
empty = Empty

export
fromNonEmpty : Lazy (Gen1 a) -> Gen a
fromNonEmpty = NonEmpty . wrapLazy (map Just)

export
toNonEmpty : Gen a -> Maybe $ Lazy (Gen1 $ Maybe a)
toNonEmpty Empty        = Nothing
toNonEmpty $ NonEmpty g = Just g

--------------------------
--- Running generators ---
--------------------------

export
unGen : MonadRandom m => MonadError () m => Gen a -> m a
unGen $ Empty      = throwError ()
unGen $ NonEmpty g = unGen g >>= maybe (throwError ()) pure

export
unGenTryAll' : RandomGen g => (seed : g) -> Gen a -> Stream (Maybe a, g)
unGenTryAll' seed gen = do
  let (seed, mc) = runRandom seed $ runMaybeT $ unGen {m=MaybeT Rand} gen
  (mc, seed) :: unGenTryAll' seed gen

export
unGenTryAll : RandomGen g => (seed : g) -> Gen a -> Stream $ Maybe a
unGenTryAll = map fst .: unGenTryAll'

export
unGenTryN : RandomGen g => (n : Nat) -> g -> Gen a -> LazyList a
unGenTryN n = mapMaybe id .: take (limit n) .: unGenTryAll

-- TODO To add config and Reader for that.
--      This config should contain attempts count for each `unGen` (including those in combinators)
--      Current `unGen` should be renamed to `unGen1` and not be exported.
--      Current `unGenTryN` should be changed returning `LazyList (a, g)` and
--      new `unGen` should be implemented trying `retry` times from config using this (`g` must be stored to restore correct state of seed).

---------------------------------------
--- Standard combination interfaces ---
---------------------------------------

export
Functor Gen where
  map _ $ Empty      = Empty
  map f $ NonEmpty g = NonEmpty $ map @{Compose} f g

export
Applicative Gen where
  pure x = NonEmpty $ pure @{Compose} x

  Empty <*> _ = Empty
  _ <*> Empty = Empty

  NonEmpty gf <*> NonEmpty ga = NonEmpty $ (gf <*> ga) @{Compose}

export
Monad Gen where
  Empty      >>= _  = Empty
  NonEmpty g >>= nf = NonEmpty $ (>>=) @{Compose} g $ maybe (pure Nothing) force . toNonEmpty . nf

---------------------------------------------
--- Data type for alternatives in `oneOf` ---
---------------------------------------------

namespace GenAlternatives

  export
  record GenAlternatives' a where
    constructor MkGenAlts
    unGenAlts : GenAlternatives' False $ Maybe a

  export %inline
  Nil : GenAlternatives' a
  Nil = MkGenAlts []

  export
  (::) : Gen a -> Lazy (GenAlternatives' a) -> GenAlternatives' a
  Empty      :: xs = xs
  NonEmpty x :: xs = MkGenAlts $ relax $ x :: xs.unGenAlts

  -- This concatenation breaks relative proportions in frequences of given alternative lists
  public export %inline
  (++) : GenAlternatives' a -> Lazy (GenAlternatives' a) -> GenAlternatives' a
  xs ++ ys = MkGenAlts $ xs.unGenAlts ++ ys.unGenAlts

  public export %inline
  length : GenAlternatives' a -> Nat
  length $ MkGenAlts alts = length alts

  export %inline
  Functor GenAlternatives' where
    map f $ MkGenAlts xs = MkGenAlts $ map f xs @{Compose}

  export %inline
  Applicative GenAlternatives' where
    pure = MkGenAlts . pure @{Compose}
    MkGenAlts xs <*> MkGenAlts ys = MkGenAlts $ (xs <*> ys) @{Compose}

  export %inline
  Alternative GenAlternatives' where
    empty = MkGenAlts empty
    MkGenAlts xs <|> ys = MkGenAlts $ xs <|> ys.unGenAlts

  export %inline
  Monad GenAlternatives' where
    MkGenAlts xs >>= f = MkGenAlts $ flip processAlternatives' xs $ relax . alternativesOf . (>>= oneOf' . traverse f) where
      %inline oneOf' : forall a. GenAlternatives' (Maybe a) -> Gen1 (Maybe a)
      oneOf' $ MkGenAlts xs = case strengthen xs of
        Nothing => pure Nothing
        Just xs => oneOf $ join <$> xs

----------------------------------
--- Creation of new generators ---
----------------------------------

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export %inline
oneOf : {default Nothing description : Maybe String} -> GenAlternatives' a -> Gen a
oneOf = maybe empty (NonEmpty . delay . oneOf {description}) . strengthen . unGenAlts

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : {default Nothing description : Maybe String} -> LazyList (Nat, Gen a) -> Gen a
frequency xs = maybe empty (NonEmpty . delay . frequency {description}) $
                 strengthen $ fromLazyList $ mapMaybe {b=(_, Lazy _)} (\(w, g) => [| (toPosNat w, toNonEmpty g) |]) xs

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : {default Nothing description : Maybe String} -> List a -> Gen a
elements xs = oneOf {description} $ MkGenAlts $ altsFromList $ relaxF $ fromList $ map Just xs

export %inline
elements' : Foldable f => {default Nothing description : Maybe String} -> f a -> Gen a
elements' = elements {description} . toList

------------------------------
--- Analysis of generators ---
------------------------------

export
alternativesOf : Gen a -> GenAlternatives' a
alternativesOf $ Empty      = []
alternativesOf $ NonEmpty g = MkGenAlts $ relax $ alternativesOf g

||| Any depth alternatives fetching.
|||
||| Alternatives of depth `0` are meant to be a single-item alternatives list with the original generator,
||| alternatives of depth `1` are those returned by the `alternativesOf` function,
||| alternatives of depth `n+1` are alternatives of all alternatives of depth `n` being flattened into a single alternatives list.
export
deepAlternativesOf : (depth : Nat) -> Gen a -> GenAlternatives' a
deepAlternativesOf _ $ Empty      = []
deepAlternativesOf n $ NonEmpty g = MkGenAlts $ relax $ deepAlternativesOf n g

||| Returns generator with internal structure hidden (say, revealed by `alternativesOf`),
||| except for empty generator, which would still be returned as empty generator.
export
forgetStructure : Gen a -> Gen a
forgetStructure $ Empty      = Empty
forgetStructure $ NonEmpty g = NonEmpty $ forgetStructure g

public export
processAlternatives : (Gen a -> Gen b) -> Gen a -> GenAlternatives' b
processAlternatives f = MkGenAlts . processAlternativesMaybe (toNonEmpty . f . NonEmpty . delay) . unGenAlts . alternativesOf

public export
mapAlternativesOf : (a -> b) -> Gen a -> GenAlternatives' b
mapAlternativesOf = processAlternatives . map

public export %inline
mapAlternativesWith : Gen a -> (a -> b) -> GenAlternatives' b
mapAlternativesWith = flip mapAlternativesOf

-- Priority is chosen to be able to use these operators without parenthesis
-- in expressions of lists, i.e. involving operators `::` and `++`.
infix 8 `mapAlternativesOf`
      , `mapAlternativesWith`

-----------------
--- Filtering ---
-----------------

export
mapMaybe : (a -> Maybe b) -> Gen a -> Gen b
mapMaybe f g = maybe empty pure . f =<< g

export
suchThat_withPrf : Gen a -> (p : a -> Bool) -> Gen $ a `Subset` So . p
suchThat_withPrf g p = mapMaybe lp g where
  lp : a -> Maybe $ a `Subset` So . p
  lp x with (p x) proof prf
    lp x | True  = Just $ Element x $ eqToSo prf
    lp x | False = Nothing

infixl 4 `suchThat`

public export
suchThat : Gen a -> (a -> Bool) -> Gen a
suchThat g p = fst <$> suchThat_withPrf g p

export
suchThat_dec : Gen a -> ((x : a) -> Dec (prop x)) -> Gen $ Subset a prop
suchThat_dec g f = mapMaybe d g where
  d : a -> Maybe $ Subset a prop
  d x = case f x of
    Yes p => Just $ Element x p
    No  _ => Nothing

||| Filters the given generator so, that resulting values `x` are solutions of equation `y = f x` for given `f` and `y`.
export
suchThat_invertedEq : DecEq b => Gen a -> (y : b) -> (f : a -> b) -> Gen $ Subset a $ \x => y = f x
suchThat_invertedEq g y f = g `suchThat_dec` \x => y `decEq` f x

-------------------------------
--- Variation in generation ---
-------------------------------

-- TODO to reimplement `variant` to ensure that variant of `Uniform` is left `Uniform`.
export
variant : Nat -> Gen a -> Gen a
variant _ $ Empty      = Empty
variant n $ NonEmpty g = NonEmpty $ variant n g

-----------------------------
--- Particular generators ---
-----------------------------

export
listOf : {default (choose (0, 10)) length : Gen Nat} -> Gen a -> Gen (List a)
listOf g = sequence $ List.replicate !length g

export
vectOf : {n : Nat} -> Gen a -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
