module Test.DepTyCheck.Gen.NonEmpty

import Control.Function.FunExt

import Control.Monad.State
import public Control.Monad.State.Interface
import public Control.Monad.Error.Interface
import Control.Monad.Maybe

import Data.DPair
import Data.Nat.Pos
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

public export %inline
wrapLazy : (a -> b) -> Lazy a -> Lazy b
wrapLazy f = delay . f . force

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

record OneOfAlternatives (0 a : Type)

export
data Gen : Type -> Type where
  Empty : Gen a
  Pure  : a -> Gen a
  Point : (forall g, m. RandomGen g => MonadState g m => MonadError () m => m a) -> Gen a
  OneOf : OneOfAlternatives a -> Gen a
  Bind  : Gen c -> (c -> Gen a) -> Gen a

record OneOfAlternatives (0 a : Type) where
  constructor MkOneOf
  totalWeight : Nat
  gens : List1 (PosNat, Lazy (Gen a))
  {auto 0 weightCorrect : totalWeight = foldl1 (+) (gens <&> \x => fst $ fst x)}

-- TODO To think about arbitrary discrete final probability distribution instead of only uniform.

------------------------------------------------
--- Technical stuff for mapping alternatives ---
------------------------------------------------

mapTaggedLazy : (a -> b) -> List1 (tag, Lazy a) -> List1 (tag, Lazy b)
mapTaggedLazy = map . mapSnd . wrapLazy

0 mapExt : (xs : List _) -> ((x : _) -> f x = g x) -> map f xs = map g xs
mapExt []      _  = Refl
mapExt (x::xs) fg = rewrite fg x in cong (g x ::) $ mapExt _ fg

0 mapTaggedLazy_preserves_tag : {cf : _} ->
                                {ff : _} ->
                                {mf : _} ->
                                (xs : List1 (tag, Lazy a)) ->
                                foldl1 cf (xs <&> \x => ff $ fst x) = foldl1 cf (mapTaggedLazy mf xs <&> \x => ff $ fst x)
mapTaggedLazy_preserves_tag ((t, x):::xs) = do
  rewrite mapFusion (ff . Builtin.fst) (mapSnd $ wrapLazy mf) xs
  cong (foldl {t=List} cf (ff t)) $ mapExt xs $ \(tt, xx) => Refl

0 mapTaggedLazy_preserves_w : {xs : List1 (PosNat, Lazy (Gen a))} ->
                              val = foldl1 (+) (xs <&> \x => fst $ fst x) =>
                              val = foldl1 (+) (mapTaggedLazy mf xs <&> \x => fst $ fst x)
mapTaggedLazy_preserves_w @{prf} = rewrite sym $ mapTaggedLazy_preserves_tag {cf=(+)} {ff=fst} {mf} xs in prf

mapOneOf : OneOfAlternatives a -> (Gen a -> Gen b) -> Gen b
mapOneOf (MkOneOf tw gs) f = OneOf $ MkOneOf tw @{mapTaggedLazy_preserves_w {mf=f}} $ mapTaggedLazy f gs

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
unGen $ Empty    = throwError ()
unGen $ Pure x   = pure x
unGen $ Point sf = sf
unGen $ OneOf oo = assert_total unGen . force . pickWeighted oo.gens . finToNat =<< randomFin {n=oo.totalWeight}
unGen $ Bind x f = unGen x >>= assert_total unGen . f

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
  map _ $ Empty    = Empty
  map f $ Pure x   = Pure $ f x
  map f $ Point sf = Point $ f <$> sf
  map f $ OneOf oo = mapOneOf oo $ assert_total $ map f
  map f $ Bind x g = Bind x $ assert_total map f . g

export
Applicative Gen where
  pure = Pure

  Empty <*> _ = Empty
  _ <*> Empty = Empty

  Pure f <*> g = f <$> g
  g <*> Pure x = g <&> \f => f x

  Point sfl <*> Point sfr = Point $ sfl <*> sfr

  OneOf oo <*> g = mapOneOf oo $ assert_total (<*> g)
  g <*> OneOf oo = mapOneOf oo $ assert_total (g <*>)

  Bind x f <*> g = Bind x $ assert_total (<*> g) . f
  g <*> Bind x f = Bind x $ assert_total (g <*>) . f

export
Monad Gen where
  Empty       >>= _  = Empty
  Pure x      >>= nf = nf x
  g@(Point _) >>= nf = Bind g nf -- Point $ sf >>= unGen . nf
  OneOf oo    >>= nf = mapOneOf oo $ assert_total (>>= nf)
  Bind x f    >>= nf = x >>= \x => f x >>= nf

-----------------------------------------
--- Detour: special list of lazy gens ---
-----------------------------------------

namespace GenAlternatives

  export
  record GenAlternatives a where
    constructor MkGenAlternatives
    unGenAlternatives : List (PosNat, Lazy (Gen a))

  export %inline
  Nil : GenAlternatives a
  Nil = MkGenAlternatives []

  export %inline
  (::) : Lazy (Gen a) -> GenAlternatives a -> GenAlternatives a
  x :: MkGenAlternatives xs = MkGenAlternatives $ (Element 1 ItIsSucc, x) :: xs

  -- This concatenation breaks relative proportions in frequences of given alternative lists
  public export
  (++) : GenAlternatives a -> GenAlternatives a -> GenAlternatives a
  MkGenAlternatives xs ++ MkGenAlternatives ys = MkGenAlternatives $ xs ++ ys

  public export
  length : GenAlternatives a -> Nat
  length = length . unGenAlternatives

  export
  Semigroup (GenAlternatives a) where
    xs <+> ys = xs ++ ys

  export
  Monoid (GenAlternatives a) where
    neutral = []

  export
  processAlternatives : (Gen a -> Gen b) -> GenAlternatives a -> GenAlternatives b
  processAlternatives f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapSnd (wrapLazy f)

  export
  processAlternatives' : (Gen a -> GenAlternatives b) -> GenAlternatives a -> GenAlternatives b
  processAlternatives' f = concat . mapGens where

    mapWeight : forall a. (PosNat -> PosNat) -> GenAlternatives a -> GenAlternatives a
    mapWeight f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapFst f

    mapGens : GenAlternatives a -> List $ GenAlternatives b
    mapGens $ MkGenAlternatives xs = xs <&> \(w, x) => mapWeight (w *) $ f x

export
Cast (List a) (GenAlternatives a) where
  cast []      = []
  cast (x::xs) = pure x :: cast xs

----------------------------------
--- Creation of new generators ---
----------------------------------

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export
oneOf : GenAlternatives a -> Gen a
oneOf alts = case normaliseWeights $ unGenAlternatives alts of
               []       => empty
               [(_, x)] => x
               x::xs    => OneOf $ MkOneOf _ $ x:::xs

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : List (Nat, Lazy (Gen a)) -> Gen a
frequency = oneOf . fromList where
  fromList : List (Nat, Lazy (Gen a)) -> GenAlternatives a
  fromList = MkGenAlternatives . mapMaybe (\(w, x) => (, x) <$> toPosNat w)

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
alternativesOf $ Empty    = []
alternativesOf $ OneOf oo = MkGenAlternatives $ forget oo.gens
alternativesOf g          = [g]

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
  pure x = [ pure x ]
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
mapMaybe _ $ Empty    = Empty
mapMaybe p $ Pure x   = maybe Empty Pure $ p x
mapMaybe p $ Point sf = Point $ sf >>= maybe (throwError ()) pure . p
mapMaybe p $ OneOf oo = mapOneOf oo $ assert_total mapMaybe p
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
