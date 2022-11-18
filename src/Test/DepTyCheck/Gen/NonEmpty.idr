module Test.DepTyCheck.Gen.NonEmpty

import Control.Monad.State
import public Control.Monad.State.Interface

import Data.Nat.Pos
import Data.List
import Data.List.CheckedEmpty
import Data.Vect
import Data.Stream

import public System.Random.Simple

%default total

-------------------------
--- Utility functions ---
-------------------------

randomFin : RandomGen g => MonadState g m => (n : PosNat) -> m $ Fin $ fst n
randomFin $ Element (S _) _ = random'

public export %inline
wrapLazy : (a -> b) -> Lazy a -> Lazy b
wrapLazy f = delay . f . force

---------------------------------------
--- Definition of the `NonEmptyGen` ---
---------------------------------------

record OneOfAlternatives (0 a : Type)

export
data NonEmptyGen : Type -> Type where
  Pure  : a -> NonEmptyGen a
  Point : (forall g, m. RandomGen g => MonadState g m => m a) -> NonEmptyGen a
  OneOf : OneOfAlternatives a -> NonEmptyGen a
  Bind  : NonEmptyGen c -> (c -> NonEmptyGen a) -> NonEmptyGen a

record OneOfAlternatives (0 a : Type) where
  constructor MkOneOf
  totalWeight : PosNat
  gens : NEList (PosNat, Lazy (NonEmptyGen a))
  {auto 0 weightCorrect : totalWeight = foldl1 (+) (gens <&> \x => fst x)}

-- TODO To think about arbitrary discrete final probability distribution instead of only uniform.

------------------------------------------------
--- Technical stuff for mapping alternatives ---
------------------------------------------------

mapTaggedLazy : (a -> b) -> NEList (tag, Lazy a) -> NEList (tag, Lazy b)
mapTaggedLazy = map . mapSnd . wrapLazy

mapOneOf : OneOfAlternatives a -> (NonEmptyGen a -> NonEmptyGen b) -> NonEmptyGen b
mapOneOf (MkOneOf tw gs @{prf}) f = OneOf $ MkOneOf tw (mapTaggedLazy f gs) @{do
    rewrite mapFusion (Builtin.fst) (mapSnd $ wrapLazy f) gs
    rewrite prf
    cong (CheckedEmpty.foldl1 (+)) $ mapExt gs $ \(_, _) => Refl
  }

-----------------------------
--- Very basic generators ---
-----------------------------

export
chooseAny : Random a => NonEmptyGen a
chooseAny = Point random'

export
choose : Random a => (a, a) -> NonEmptyGen a
choose bounds = Point $ randomR' bounds

--------------------------
--- Running generators ---
--------------------------

export
unGen : RandomGen g => MonadState g m => NonEmptyGen a -> m a
unGen $ Pure x   = pure x
unGen $ Point sf = sf
unGen $ OneOf oo = assert_total unGen . force . pickWeighted oo.gens . finToNat =<< randomFin oo.totalWeight
unGen $ Bind x f = unGen x >>= assert_total unGen . f

-- TODO To add config and Reader for that.
--      This config should contain attempts count for each `unGen` (including those in combinators)
--      Current `unGen` should be renamed to `unGen1` and not be exported.
--      Current `unGenTryN` should be changed returning `LazyList (a, g)` and
--      new `unGen` should be implemented trying `retry` times from config using this (`g` must be stored to restore correct state of seed).

---------------------------------------
--- Standard combination interfaces ---
---------------------------------------

export
Functor NonEmptyGen where
  map f $ Pure x   = Pure $ f x
  map f $ Point sf = Point $ f <$> sf
  map f $ OneOf oo = mapOneOf oo $ assert_total $ map f
  map f $ Bind x g = Bind x $ assert_total map f . g

export
Applicative NonEmptyGen where
  pure = Pure

  Pure f <*> g = f <$> g
  g <*> Pure x = g <&> \f => f x

  Point sfl <*> Point sfr = Point $ sfl <*> sfr

  OneOf oo <*> g = mapOneOf oo $ assert_total (<*> g)
  g <*> OneOf oo = mapOneOf oo $ assert_total (g <*>)

  Bind x f <*> g = Bind x $ assert_total (<*> g) . f
  g <*> Bind x f = Bind x $ assert_total (g <*>) . f

export
Monad NonEmptyGen where
  Pure x      >>= nf = nf x
  g@(Point _) >>= nf = Bind g nf -- Point $ sf >>= unGen . nf
  OneOf oo    >>= nf = mapOneOf oo $ assert_total (>>= nf)
  Bind x f    >>= nf = x >>= \x => f x >>= nf

-----------------------------------------
--- Detour: special list of lazy gens ---
-----------------------------------------

namespace GenAlternatives

  export
  record GenAlternatives' (0 mustBeNotEmpty : Bool) a where
    constructor MkGenAlternatives
    unGenAlternatives : CEList mustBeNotEmpty (PosNat, Lazy (NonEmptyGen a))

  public export %inline
  GenAlternatives : Type -> Type
  GenAlternatives = GenAlternatives' True

  export %inline
  Nil : GenAlternatives' False a
  Nil = MkGenAlternatives []

  export %inline
  (::) : Lazy (NonEmptyGen a) -> GenAlternatives' ne a -> GenAlternatives a
  x :: MkGenAlternatives xs = MkGenAlternatives $ (Element 1 ItIsSucc, x) :: xs

  -- This concatenation breaks relative proportions in frequences of given alternative lists
  public export
  (++) : GenAlternatives' nel a -> GenAlternatives' ner a -> GenAlternatives' (nel || ner) a
  MkGenAlternatives xs ++ MkGenAlternatives ys = MkGenAlternatives $ xs ++ ys

  public export
  length : GenAlternatives' ne a -> Nat
  length $ MkGenAlternatives alts = length alts

  export
  processAlternatives : (NonEmptyGen a -> NonEmptyGen b) -> GenAlternatives' ne a -> GenAlternatives' ne b
  processAlternatives f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapSnd (wrapLazy f)

  export
  processAlternatives' : (NonEmptyGen a -> GenAlternatives b) -> GenAlternatives a -> GenAlternatives b
  processAlternatives' f = foldl1 (++) . mapGens where

    mapWeight : forall a. (PosNat -> PosNat) -> GenAlternatives' nea a -> GenAlternatives' nea a
    mapWeight f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapFst f

    mapGens : GenAlternatives a -> NEList $ GenAlternatives b
    mapGens $ MkGenAlternatives xs = xs <&> \(w, x) => mapWeight (w *) $ f x

export
Cast (CEList ne a) (GenAlternatives' ne a) where
  cast = MkGenAlternatives . map (\x => (1, pure x))

----------------------------------
--- Creation of new generators ---
----------------------------------

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export
oneOf : GenAlternatives a -> NonEmptyGen a
oneOf $ MkGenAlternatives [(_, x)]  = x
oneOf $ MkGenAlternatives xs@(_::_) = OneOf $ MkOneOf _ $ normaliseWeights xs

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : NEList (PosNat, Lazy (NonEmptyGen a)) -> NonEmptyGen a
frequency = oneOf . MkGenAlternatives

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : NEList a -> NonEmptyGen a
elements = oneOf . cast

------------------------------
--- Analysis of generators ---
------------------------------

export
alternativesOf : NonEmptyGen a -> GenAlternatives a
alternativesOf $ OneOf oo = MkGenAlternatives oo.gens
alternativesOf g          = [g]

||| Any depth alternatives fetching.
|||
||| Alternatives of depth `0` are meant to be a single-item alternatives list with the original generator,
||| alternatives of depth `1` are those returned by the `alternativesOf` function,
||| alternatives of depth `n+1` are alternatives of all alternatives of depth `n` being flattened into a single alternatives list.
export
deepAlternativesOf : (depth : Nat) -> NonEmptyGen a -> GenAlternatives a
deepAlternativesOf 0     gen   = [ gen ]
deepAlternativesOf 1     gen   = alternativesOf gen
deepAlternativesOf (S k) gen   = processAlternatives' alternativesOf $ deepAlternativesOf k gen

||| Returns generator with internal structure hidden (say, revealed by `alternativesOf`),
||| except for empty generator, which would still be returned as empty generator.
export
forgetStructure : NonEmptyGen a -> NonEmptyGen a
forgetStructure g@(Point _) = g
forgetStructure g = Point $ unGen g

public export
processAlternatives : (NonEmptyGen a -> NonEmptyGen b) -> NonEmptyGen a -> GenAlternatives b
processAlternatives f = processAlternatives f . alternativesOf

public export
mapAlternativesOf : (a -> b) -> NonEmptyGen a -> GenAlternatives b
mapAlternativesOf = processAlternatives . map

public export %inline
mapAlternativesWith : NonEmptyGen a -> (a -> b) -> GenAlternatives b
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
Monad GenAlternatives where
  xs >>= f = flip processAlternatives' xs $ alternativesOf . (>>= oneOf . f)

-------------------------------
--- Variation in generation ---
-------------------------------

-- TODO to reimplement `variant` to ensure that variant of `Uniform` is left `Uniform`.
export
variant : Nat -> NonEmptyGen a -> NonEmptyGen a
variant Z       gen = gen
variant x@(S _) gen = Point $ modify (index x . iterate (fst . next)) *> unGen gen

-----------------------------
--- Particular generators ---
-----------------------------

export
listOf : {default (choose (0, 10)) length : NonEmptyGen Nat} -> NonEmptyGen a -> NonEmptyGen (List a)
listOf g = sequence $ List.replicate !length g

export
vectOf : {n : Nat} -> NonEmptyGen a -> NonEmptyGen (Vect n a)
vectOf g = sequence $ replicate n g
