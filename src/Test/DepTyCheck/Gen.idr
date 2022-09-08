module Test.DepTyCheck.Gen

import Control.Function.FunExt

import Control.Monad.State
import public Control.Monad.State.Interface
import public Control.Monad.Error.Interface
import Control.Monad.Maybe

import Data.DPair
import Data.List
import Data.List1
import Data.List.Lazy
import Data.Vect
import Data.Stream

import Decidable.Equality

import public System.Random.Simple

%default total

-------------------------
--- Utility functions ---
-------------------------

randomFin : RandomGen g => MonadState g m => MonadError () m => {n : _} -> m $ Fin n
randomFin {n = Z}   = throwError ()
randomFin {n = S k} = random'

pickUniformly : RandomGen g => MonadState g m => MonadError () m => List a -> m a
pickUniformly xs = index' xs <$> randomFin

public export
wrapLazy : (a -> b) -> Lazy a -> Lazy b
wrapLazy f = delay . f . force

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

export
data Gen : Type -> Type where
  Point : (forall g, m. RandomGen g => MonadState g m => MonadError () m => m a) -> Gen a
  OneOf : List1 (Lazy (Gen a)) -> Gen a
  Bind  : Gen c -> (c -> Gen a) -> Gen a

-- TODO To think about arbitrary discrete final probability distribution instead of only uniform.

export
chooseAny : Random a => Gen a
chooseAny = Point random'

export
choose : Random a => (a, a) -> Gen a
choose bounds = Point $ randomR' bounds

export
empty : Gen a
empty = Point $ throwError ()

export
unGen : RandomGen g => MonadState g m => MonadError () m => Gen a -> m a
unGen $ Point sf = sf
unGen $ OneOf gs = pickUniformly (forget gs) >>= assert_total unGen . force
unGen $ Bind x f = unGen x >>= assert_total unGen . f

export
unGenTryN : RandomGen g => (n : Nat) -> g -> Gen a -> LazyList a
unGenTryN n seed gen = mapMaybe id $ go n seed where
  go : Nat -> g -> LazyList $ Maybe a
  go Z     _    = []
  go (S n) seed = do
    let (seed, mc) = runState seed $ runMaybeT $ unGen {g} {m=MaybeT $ State g} gen
    mc :: go n seed

-- TODO To add config and Reader for that.
--      This config should contain attempts count for each `unGen` (including those in combinators)
--      Current `unGen` should be renamed to `unGen1` and not be exported.
--      Current `unGenTryN` should be changed returning `LazyList (a, g)` and
--      new `unGen` should be implemented trying `retry` times from config using this (`g` must be stored to restore correct state of seed).

export
Functor Gen where
  map f $ Point sf = Point $ f <$> sf
  map f $ OneOf gs = OneOf $ wrapLazy (assert_total map f) <$> gs
  map f $ Bind x g = Bind x $ assert_total map f . g

export
Applicative Gen where
  pure x = Point $ pure x

  Point sfl <*> Point sfr = Point $ sfl <*> sfr

  OneOf gs <*> g = OneOf $ gs <&> wrapLazy (assert_total (<*> g))
  g <*> OneOf gs = OneOf $ gs <&> wrapLazy (assert_total (g <*>))

  Bind x f <*> g = Bind x $ assert_total (<*> g) . f
  g <*> Bind x f = Bind x $ assert_total (g <*>) . f

export
Monad Gen where
  g@(Point _) >>= nf = Bind g nf -- Point $ sf >>= unGen . nf
  OneOf gs    >>= nf = OneOf $ gs <&> wrapLazy (assert_total (>>= nf))
  Bind x f    >>= nf = Bind x $ assert_total $ f >=> nf

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export
oneOf : List (Lazy (Gen a)) -> Gen a
oneOf []      = empty
oneOf [x]     = x
oneOf (x::xs) = OneOf $ x:::xs

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : List (Nat, Lazy (Gen a)) -> Gen a
frequency = oneOf . concatMap (uncurry replicate)
            -- TODO to reimplement this more effectively

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : List a -> Gen a
elements = oneOf . map (delay . pure)

export
elements' : Foldable f => f a -> Gen a
elements' = elements . toList

export
alternativesOf : Gen a -> List $ Lazy (Gen a)
alternativesOf $ OneOf gs = forget gs
alternativesOf g          = [g]

public export
processAlternatives : (Gen a -> Gen b) -> Gen a -> List $ Lazy (Gen b)
processAlternatives f = map (wrapLazy f) . alternativesOf

public export
mapAlternativesOf : (a -> b) -> Gen a -> List $ Lazy (Gen b)
mapAlternativesOf = processAlternatives . map

public export
apAlternativesOf : Gen (a -> b) -> Gen a -> List $ Lazy (Gen b)
apAlternativesOf = processAlternatives . (<*>)

public export
bindAlternativesOf : (a -> Gen b) -> Gen a -> List $ Lazy (Gen b)
bindAlternativesOf = processAlternatives . (=<<)

public export %inline
mapAlternativesWith : Gen a -> (a -> b) -> List $ Lazy (Gen b)
mapAlternativesWith = flip mapAlternativesOf

public export %inline
apAlternativesWith : Gen a -> Gen (a -> b) -> List $ Lazy (Gen b)
apAlternativesWith = flip apAlternativesOf

public export %inline
bindAlternativesWith : Gen a -> (a -> Gen b) -> List $ Lazy (Gen b)
bindAlternativesWith = flip bindAlternativesOf

export
forgetStructure : Gen a -> Gen a
forgetStructure g@(Point _) = g
forgetStructure g = Point $ unGen g

public export
mapForgottenStructureOf : (a -> b) -> Gen a -> Gen b
mapForgottenStructureOf f = map f . forgetStructure

public export %inline
mapForgottenStructureWith : Gen a -> (a -> b) -> Gen b
mapForgottenStructureWith = flip mapForgottenStructureOf

-- Priority is chosen to be able to use these operators without parenthesis
-- in expressions of lists, i.e. involving operators `::` and `++`.
infix 8 `mapAlternativesOf`
      , `mapAlternativesWith`

      , `apAlternativesOf`
      , `apAlternativesWith`

      , `bindAlternativesOf`
      , `bindAlternativesWith`

      , `mapForgottenStructureOf`
      , `mapForgottenStructureWith`

export
mapMaybe : (a -> Maybe b) -> Gen a -> Gen b
mapMaybe p $ Point sf = Point $ sf >>= maybe (throwError ()) pure . p
mapMaybe p $ OneOf gs = OneOf $ gs <&> wrapLazy (assert_total mapMaybe p)
mapMaybe p $ Bind x f = Bind x $ assert_total mapMaybe p . f

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

-- TODO to reimplement `variant` to ensure that variant of `Uniform` is left `Uniform`.
export
variant : Nat -> Gen a -> Gen a
variant Z       gen = gen
variant x@(S _) gen = Point $ modify (index x . iterate (fst . next)) *> unGen gen

export
listOf : {default (choose (0, 10)) length : Gen Nat} -> Gen a -> Gen (List a)
listOf g = sequence $ List.replicate !length g

export
vectOf : {n : Nat} -> Gen a -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
