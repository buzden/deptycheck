module Test.DepTyCheck.Gen

import Control.Function.FunExt

import Control.Monad.State
import public Control.Monad.State.Interface
import public Control.Monad.Error.Interface
import Control.Monad.Maybe

import Data.DPair
import Data.Fuel
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

pickUniformly : List1 (Subset Nat IsSucc, a) -> Nat -> a
pickUniformly ((_, x):::[])                  _ = x
pickUniformly w@((Element n _, x):::(y::ys)) k = if k <= n then x else pickUniformly (assert_smaller w $ y:::ys) (k `minus` n)

public export %inline
wrapLazy : (a -> b) -> Lazy a -> Lazy b
wrapLazy f = delay . f . force

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

export
data Gen : Type -> Type where
  Empty : Gen a
  Pure  : a -> Gen a
  Point : (forall g, m. RandomGen g => MonadState g m => MonadError () m => m a) -> Gen a
  OneOf : (totalWeight : Nat) ->
          (gens : List1 (Subset Nat IsSucc, Lazy (Gen a))) ->
          (0 _ : totalWeight = foldl1 (+) (gens <&> \x => fst $ fst x)) =>
          Gen a
  Bind  : Gen c -> (c -> Gen a) -> Gen a

-- TODO To think about arbitrary discrete final probability distribution instead of only uniform.

------------------------------------------------
--- Technical stuff for mapping alternatives ---
------------------------------------------------

mapLNLG : (a -> b) -> List1 (tag, Lazy a) -> List1 (tag, Lazy b)
mapLNLG = map . mapSnd . wrapLazy

0 mapExt : {xs : List _} -> ((x : _) -> f x = g x) -> map f xs = map g xs
mapExt {xs = []}    _  = Refl
mapExt {xs = x::xs} fg = rewrite fg x in cong (g x ::) $ mapExt fg

0 mapLNLG_preserves_tag : {cf : _} ->
                          {ff : _} ->
                          {mf : _} ->
                          (xs : List1 (tag, Lazy a)) ->
                          foldl1 cf (xs <&> \x => ff $ fst x) = foldl1 cf (mapLNLG mf xs <&> \x => ff $ fst x)
mapLNLG_preserves_tag ((t, x):::xs) = do
  rewrite mapFusion (ff . Builtin.fst) (mapSnd $ wrapLazy mf) xs
  cong (foldl {t=List} cf (ff t)) $ mapExt {xs} $ \(tt, xx) => Refl

0 mapLNLG_preserves_w : {xs : List1 (Subset Nat IsSucc, Lazy (Gen a))} ->
                        val = foldl1 (+) (xs <&> \x => fst $ fst x) =>
                        val = foldl1 (+) (mapLNLG mf xs <&> \x => fst $ fst x)
mapLNLG_preserves_w @{prf} = rewrite sym $ mapLNLG_preserves_tag {cf=(+)} {ff=fst} {mf} xs in prf

data IsOneOf : Gen a -> Type where
  ItIsOneOf : IsOneOf $ OneOf tw gs @{twCorr}

mapOneOf : (g : Gen a) -> (Gen a -> Gen b) -> (0 _ : IsOneOf g) => Gen b
mapOneOf (OneOf tw gs) f = OneOf tw @{mapLNLG_preserves_w {mf=f}} $ mapLNLG f gs

-----------------------------
--- Very basic generators ---
-----------------------------

export
chooseAny : Random a => Gen a
chooseAny = Point random'

export
choose : Random a => (a, a) -> Gen a
choose bounds = Point $ randomR' bounds

export
empty : Gen a
empty = Empty

--------------------------
--- Running generators ---
--------------------------

export
unGen : RandomGen g => MonadState g m => MonadError () m => Gen a -> m a
unGen $ Empty       = throwError ()
unGen $ Pure x      = pure x
unGen $ Point sf    = sf
unGen $ OneOf tw gs = randomFin {n=tw} >>= assert_total unGen . force . pickUniformly gs . finToNat
unGen $ Bind x f    = unGen x >>= assert_total unGen . f

export
unGenTryAll' : RandomGen g => (seed : g) -> Gen a -> Stream (Maybe a, g)
unGenTryAll' seed gen = do
  let (seed, mc) = runState seed $ runMaybeT $ unGen {g} {m=MaybeT $ State g} gen
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
  map _ $ Empty       = Empty
  map f $ Pure x      = Pure $ f x
  map f $ Point sf    = Point $ f <$> sf
  map f g@(OneOf _ _) = mapOneOf g $ assert_total $ map f
  map f $ Bind x g    = Bind x $ assert_total map f . g

export
Applicative Gen where
  pure = Pure

  Empty <*> _ = Empty
  _ <*> Empty = Empty

  Pure f <*> g = f <$> g
  g <*> Pure x = g <&> \f => f x

  Point sfl <*> Point sfr = Point $ sfl <*> sfr

  o@(OneOf _ _) <*> g = mapOneOf o $ assert_total (<*> g)
  g <*> o@(OneOf _ _) = mapOneOf o $ assert_total (g <*>)

  Bind x f <*> g = Bind x $ assert_total (<*> g) . f
  g <*> Bind x f = Bind x $ assert_total (g <*>) . f

export
Monad Gen where
  Empty         >>= _  = Empty
  Pure x        >>= nf = nf x
  g@(Point _)   >>= nf = Bind g nf -- Point $ sf >>= unGen . nf
  o@(OneOf _ _) >>= nf = mapOneOf o $ assert_total (>>= nf)
  Bind x f      >>= nf = x >>= \x => f x >>= nf

-----------------------------------------
--- Detour: special list of lazy gens ---
-----------------------------------------

namespace GenAlternatives

  public export
  data GenAlternatives : Type -> Type where
    Nil  : GenAlternatives a
    Cons : Lazy (Gen a) -> (weight : Nat) -> GenAlternatives a -> GenAlternatives a

  -- This concatenation breaks relative proportions in frequences of given alternative lists
  public export
  (++) : GenAlternatives a -> GenAlternatives a -> GenAlternatives a
  (++) []                 ys = ys
  (++) (Cons x weight xs) ys = Cons x weight (xs ++ ys)

  public export
  length : GenAlternatives a -> Nat
  length []           = Z
  length (Cons _ _xs) = S $ length xs

  export
  Semigroup (GenAlternatives a) where
    xs <+> ys = xs ++ ys

  export
  Monoid (GenAlternatives a) where
    neutral = []

  export
  processAlternatives : (Gen a -> Gen b) -> GenAlternatives a -> GenAlternatives b
  processAlternatives _   []               = []
  processAlternatives f $ Cons x weight xs = Cons (wrapLazy f x) weight (processAlternatives f xs)

  export
  processAlternatives' : (Gen a -> GenAlternatives b) -> GenAlternatives a -> GenAlternatives b
  processAlternatives' f = concat . mapGens where

    mapWeight : forall a. (Nat -> Nat) -> GenAlternatives a -> GenAlternatives a
    mapWeight _ []                 = []
    mapWeight f $ Cons x weight xs = Cons x (f weight) (mapWeight f xs)

    mapGens : GenAlternatives a -> List $ GenAlternatives b
    mapGens []                 = []
    mapGens $ Cons x weight xs = mapWeight (weight *) (f x) :: mapGens xs

  --- Lists syntax for alternatives list ---

  export
  interface GenAlternative g where
    altGen : g a -> Lazy (Gen a)
    weight : g a -> Nat

  public export %inline
  (::) : GenAlternative g => g a -> GenAlternatives a -> GenAlternatives a
  (::) @{ga} x xs = Cons (altGen x) (weight @{ga} x) xs

  namespace Gen

    export
    GenAlternative (\a => Lazy (Gen a)) where
      altGen = id
      weight = const 1

    export
    GenAlternative Gen where
      altGen = delay
      weight = const 1

  namespace Weighted

    public export
    data GenWithWeight : Type -> Type where
      Weighted : Nat -> Lazy (Gen a) -> GenWithWeight a

    public export %inline
    weighted : Nat -> Lazy (Gen a) -> GenWithWeight a
    weighted = Weighted

    infixr 0 `weighted` -- right-associativity for compatibility with `$`

    public export %inline
    withWeight : Lazy (Gen a) -> Nat -> GenWithWeight a
    withWeight = flip Weighted

    infix 0 `withWeight`

    export
    GenAlternative GenWithWeight where
      altGen (Weighted _ g) = g
      weight (Weighted w _) = w

  namespace Maybe

    export
    GenAlternative (\a => Maybe (Lazy (Gen a))) where
      altGen Nothing  = empty
      altGen (Just x) = x
      weight Nothing  = 0
      weight (Just _) = 1

toLNLG : GenAlternatives a -> List (Subset Nat IsSucc, Lazy (Gen a))
toLNLG []                = []
toLNLG $ Cons _ Z     xs = toLNLG xs
toLNLG $ Cons x (S w) xs = (Element (S w) ItIsSucc, x) :: toLNLG xs

fromLNLG : List (Subset Nat IsSucc, Lazy (Gen a)) -> GenAlternatives a
fromLNLG []                = []
fromLNLG ((weight, g)::xs) = Cons g weight.fst $ fromLNLG xs

export
Cast (List a) (GenAlternatives a) where
  cast []      = []
  cast (x::xs) = Cons (pure x) 1 (cast xs)

----------------------------------
--- Creation of new generators ---
----------------------------------

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export
oneOf : GenAlternatives a -> Gen a
oneOf alts = case toLNLG alts of
               []       => empty
               [(_, x)] => x
               x::xs    => OneOf _ $ x:::xs

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
|||
||| Deprecated. Use `oneOf` with `weighted` instead, e.g.,
||| instead of `frequency [(1, g1), (2, g2)]` use `oneOf [g1, weighted 2 g2]`.
export %deprecate
frequency : List (Nat, Lazy (Gen a)) -> Gen a
frequency = oneOf . fromList where
  fromList : List (Nat, Lazy (Gen a)) -> GenAlternatives a
  fromList []           = []
  fromList ((w, g)::xs) = Cons g w $ fromList xs

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : List a -> Gen a
elements = oneOf . cast

export
elements' : Foldable f => f a -> Gen a
elements' = elements . toList

------------------------------
--- Analysis of generators ---
------------------------------

export
alternativesOf : Gen a -> GenAlternatives a
alternativesOf $ Empty      = []
alternativesOf $ OneOf _ gs = fromLNLG $ forget gs
alternativesOf g            = [g]

||| Any depth alternatives fetching.
|||
||| Alternatives of depth `0` are meant to be a single-item alternatives list with the original generator,
||| alternatives of depth `1` are those returned by the `alternativesOf` function,
||| alternatives of depth `n+1` are alternatives of all alternatives of depth `n` being flattened into a single alternatives list.
export
deepAlternativesOf : (depth : Nat) -> Gen a -> GenAlternatives a
deepAlternativesOf _     Empty = []
deepAlternativesOf 0     gen   = [ gen ]
deepAlternativesOf 1     gen   = alternativesOf gen
deepAlternativesOf (S k) gen   = processAlternatives' alternativesOf $ deepAlternativesOf k gen

||| Returns generator with internal structure hidden (say, revealed by `alternativesOf`),
||| except for empty generator, which would still be returned as empty generator.
export
forgetStructure : Gen a -> Gen a
forgetStructure g@(Point _) = g
forgetStructure Empty = Empty
forgetStructure g = Point $ unGen g

public export
processAlternatives : (Gen a -> Gen b) -> Gen a -> GenAlternatives b
processAlternatives f = processAlternatives f . alternativesOf

public export
mapAlternativesOf : (a -> b) -> Gen a -> GenAlternatives b
mapAlternativesOf = processAlternatives . map

public export %inline
mapAlternativesWith : Gen a -> (a -> b) -> GenAlternatives b
mapAlternativesWith = flip mapAlternativesOf

-- Priority is chosen to be able to use these operators without parenthesis
-- in expressions of lists, i.e. involving operators `::` and `++`.
infix 8 `mapAlternativesOf`
      , `mapAlternativesWith`

-----------------------------------------------------
--- Detour: implementations for list of lazy gens ---
-----------------------------------------------------

export
Functor GenAlternatives where
  map = processAlternatives . map

export
Applicative GenAlternatives where
  pure x = [ pure {f=Gen} x ]
  xs <*> ys = flip processAlternatives' xs $ flip processAlternatives ys . (<*>)

export
Alternative GenAlternatives where
  empty = []
  xs <|> ys = xs ++ ys

export
Monad GenAlternatives where
  xs >>= f = flip processAlternatives' xs $ alternativesOf . (>>= oneOf . f)

-----------------
--- Filtering ---
-----------------

export
mapMaybe : (a -> Maybe b) -> Gen a -> Gen b
mapMaybe _ $ Empty       = Empty
mapMaybe p $ Pure x      = maybe Empty Pure $ p x
mapMaybe p $ Point sf    = Point $ sf >>= maybe (throwError ()) pure . p
mapMaybe p o@(OneOf _ _) = mapOneOf o $ assert_total mapMaybe p
mapMaybe p $ Bind x f    = Bind x $ assert_total mapMaybe p . f

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
variant Z       gen = gen
variant x@(S _) gen = Point $ modify (index x . iterate (fst . next)) *> unGen gen

-----------------------------
--- Particular generators ---
-----------------------------

export
listOf : {default (choose (0, 10)) length : Gen Nat} -> Gen a -> Gen (List a)
listOf g = sequence $ List.replicate !length g

export
vectOf : {n : Nat} -> Gen a -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
