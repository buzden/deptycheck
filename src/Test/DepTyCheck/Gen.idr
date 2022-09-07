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
  map f $ OneOf gs = OneOf $ delay . assert_total map f . force <$> gs
  map f $ Bind x g = Bind x $ assert_total map f . g

export
Applicative Gen where
  pure x = Point $ pure x

  Point sfl <*> Point sfr = Point $ sfl <*> sfr

  OneOf gs <*> g = OneOf $ gs <&> delay . assert_total (<*> g) . force
  g <*> OneOf gs = OneOf $ gs <&> delay . assert_total (g <*>) . force

  Bind x f <*> g = Bind x $ assert_total (<*> g) . f
  g <*> Bind x f = Bind x $ assert_total (g <*>) . f

--namespace ApplicativeLaws
--
--  applicativeIdentity : (v : Gen a) -> pure Prelude.id <*> v = v
--  applicativeIdentity $ Point sf = ?applicativeIdentity_rhs_0 -- goes to identity law of `m` inside `Point`
--  applicativeIdentity $ OneOf gs = ?applicativeIdentity_rhs_1 -- goes recursively
--  applicativeIdentity $ Bind x f = ?applicativeIdentity_rhs_2 -- goes to identity law of `m` inside `Point`
--
--  applicativeComposition : (u : Gen $ b -> c) -> (v : Gen $ a -> b) -> (w : Gen a) -> pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
--  applicativeComposition (Point f)  (Point g)  (Point f1)  = ?applicativeComposition_rhs_12
--  applicativeComposition (Point f)  (Point g)  (OneOf xs)  = ?applicativeComposition_rhs_13
--  applicativeComposition (Point f)  (Point g)  (Bind x f1) = ?applicativeComposition_rhs_14
--  applicativeComposition (Point f)  (OneOf xs) (Point g)   = ?applicativeComposition_rhs_15
--  applicativeComposition (Point f)  (OneOf xs) (OneOf ys)  = ?applicativeComposition_rhs_16
--  applicativeComposition (Point f)  (OneOf xs) (Bind x g)  = ?applicativeComposition_rhs_17
--  applicativeComposition (Point f)  (Bind x g) (Point f1)  = ?applicativeComposition_rhs_18
--  applicativeComposition (Point f)  (Bind x g) (OneOf xs)  = ?applicativeComposition_rhs_19
--  applicativeComposition (Point f)  (Bind x g) (Bind y f1) = ?applicativeComposition_rhs_20
--  applicativeComposition (OneOf xs) (Point f)  (Point g)   = ?applicativeComposition_rhs_21
--  applicativeComposition (OneOf xs) (Point f)  (OneOf ys)  = ?applicativeComposition_rhs_22
--  applicativeComposition (OneOf xs) (Point f)  (Bind x g)  = ?applicativeComposition_rhs_23
--  applicativeComposition (OneOf xs) (OneOf ys) (Point f)   = ?applicativeComposition_rhs_24
--  applicativeComposition (OneOf xs) (OneOf ys) (OneOf zs)  = ?applicativeComposition_rhs_25
--  applicativeComposition (OneOf xs) (OneOf ys) (Bind x f)  = ?applicativeComposition_rhs_26
--  applicativeComposition (OneOf xs) (Bind x f) (Point g)   = ?applicativeComposition_rhs_27
--  applicativeComposition (OneOf xs) (Bind x f) (OneOf ys)  = ?applicativeComposition_rhs_28
--  applicativeComposition (OneOf xs) (Bind x f) (Bind y g)  = ?applicativeComposition_rhs_29
--  applicativeComposition (Bind x f) (Point g)  (Point f1)  = ?applicativeComposition_rhs_30
--  applicativeComposition (Bind x f) (Point g)  (OneOf xs)  = ?applicativeComposition_rhs_31
--  applicativeComposition (Bind x f) (Point g)  (Bind y f1) = ?applicativeComposition_rhs_32
--  applicativeComposition (Bind x f) (OneOf xs) (Point g)   = ?applicativeComposition_rhs_33
--  applicativeComposition (Bind x f) (OneOf xs) (OneOf ys)  = ?applicativeComposition_rhs_34
--  applicativeComposition (Bind x f) (OneOf xs) (Bind y g)  = ?applicativeComposition_rhs_35
--  applicativeComposition (Bind x f) (Bind y g) (Point f1)  = ?applicativeComposition_rhs_36
--  applicativeComposition (Bind x f) (Bind y g) (OneOf xs)  = ?applicativeComposition_rhs_37
--  applicativeComposition (Bind x f) (Bind y g) (Bind z f1) = ?applicativeComposition_rhs_38
--
--  applicativeHomomorphism : (x : a) -> (f : a -> b) -> the (Gen b) (pure f <*> pure x) === pure (f x)
--  applicativeHomomorphism x f = cong Point ?applicativeHomomorphism_rhs -- goes to homomorphism law of `m` inside `Point`
--
--  applicativeInterchange : FunExt => (u : Gen $ a -> b) -> (y : a) -> u <*> pure y = pure ($ y) <*> u
--  applicativeInterchange (Point f)  y = cong Point ?applicativeInterchange_rhs_0 -- goes to interchange law of `m` inside `Point`
--  applicativeInterchange (OneOf xs) y = cong OneOf $ cong (\arg => map arg xs) $ funExt $ \case
--    Point f  => ?applicativeInterchange_rhs_3 -- goes to interchange law of `m` inside `Point`
--    OneOf ys => cong OneOf $ cong (\arg => map arg ys) $ funExt $ \x => applicativeInterchange (assert_smaller (OneOf xs) x) y
--    Bind x f => cong (Bind x) $ funExt $ \x => applicativeInterchange (assert_smaller (OneOf xs) $ f x) y
--  applicativeInterchange (Bind x f) y = cong (Bind x) $ funExt $ \x => applicativeInterchange (f x) y

export
Monad Gen where
  g@(Point _) >>= nf = Bind g nf -- Point $ sf >>= unGen . nf
  OneOf gs    >>= nf = OneOf $ gs <&> delay . assert_total (>>= nf) . force
  Bind x f    >>= nf = Bind x $ assert_total $ f >=> nf

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
public export
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

export
forgetStructure : Gen a -> Gen a
forgetStructure g@(Point _) = g
forgetStructure g = Point $ unGen g

export
mapMaybe : (a -> Maybe b) -> Gen a -> Gen b
mapMaybe p $ Point sf = Point $ sf >>= maybe (throwError ()) pure . p
mapMaybe p $ OneOf gs = OneOf $ gs <&> delay . assert_total mapMaybe p . force
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
