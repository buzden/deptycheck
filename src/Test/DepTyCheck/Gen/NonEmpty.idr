module Test.DepTyCheck.Gen.NonEmpty

import Control.Monad.Random
import public Control.Monad.Random.Interface
import Control.Monad.State
import Control.Monad.Random
import public Control.Monad.Random.Interface
import public Control.Monad.State.Interface

import Data.Bool
import Data.Nat.Pos
import Data.List
import Data.CheckedEmpty.List.Lazy
import Data.Singleton
import Data.Stream
import Data.Vect

import public Language.Implicits.IfUnsolved

%default total

-------------------------
--- Utility functions ---
-------------------------

randomFin : MonadRandom m => (n : PosNat) -> m $ Fin $ fst n
randomFin $ Element (S _) _ = getRandom

public export %inline
wrapLazy : (a -> b) -> Lazy a -> Lazy b
wrapLazy f = delay . f . force

transport : Singleton x -> x = y -> Singleton y
transport z Refl = z

--------------------------------
--- Definition of the `Gen1` ---
--------------------------------

record RawGen a where
  [noHints]
  constructor MkRawGen
  unRawGen : forall m. MonadRandom m => m a

record OneOfAlternatives (0 a : Type)

export
data Gen1 : Type -> Type where
  [noHints]
  Pure  : a -> Gen1 a
  Raw   : RawGen a -> Gen1 a
  OneOf : OneOfAlternatives a -> Gen1 a
  Bind  : RawGen c -> (c -> Gen1 a) -> Gen1 a

record OneOfAlternatives (0 a : Type) where
  [noHints]
  constructor MkOneOf
  desc : Maybe String
  gens : LazyLst1 (PosNat, Lazy (Gen1 a))
  totalWeight : Singleton $ foldl1 (+) (gens <&> \x => fst x)

-- TODO To think about arbitrary discrete final probability distribution instead of only uniform.

------------------------------------------------
--- Technical stuff for mapping alternatives ---
------------------------------------------------

mapTaggedLazy : (a -> b) -> LazyLst1 (tag, Lazy a) -> LazyLst1 (tag, Lazy b)
mapTaggedLazy = map . mapSnd . wrapLazy

mapOneOf : OneOfAlternatives a -> (Gen1 a -> Gen1 b) -> Gen1 b
mapOneOf (MkOneOf desc gs tw) f = OneOf $ MkOneOf desc (mapTaggedLazy f gs) $ do
    rewrite mapFusion (Builtin.fst) (mapSnd $ wrapLazy f) gs
    transport tw $ cong (Lazy.foldl1 (+)) $ mapExt gs $ \(_, _) => Refl

-----------------------------
--- Very basic generators ---
-----------------------------

export
chooseAny : Random a => Gen1 a
chooseAny = Raw $ MkRawGen getRandom

export
choose : Random a => (a, a) -> Gen1 a
choose bounds = Raw $ MkRawGen $ getRandomR bounds

--------------------------
--- Running generators ---
--------------------------

export
unGen : MonadRandom m => Gen1 a -> m a
unGen $ Pure x   = pure x
unGen $ Raw sf   = sf.unRawGen
unGen $ OneOf oo = assert_total unGen . force . pickWeighted oo.gens . finToNat =<< randomFin oo.totalWeight.unVal
unGen $ Bind x f = x.unRawGen >>= unGen . f

export
unGenTryAll' : RandomGen g => (seed : g) -> Gen1 a -> Stream (a, g)
unGenTryAll' seed gen = do
  let (seed, mc) = runRandom seed $ unGen gen
  (mc, seed) :: unGenTryAll' seed gen

export
unGenTryAll : RandomGen g => (seed : g) -> Gen1 a -> Stream a
unGenTryAll = map fst .: unGenTryAll'

-- TODO To add config and Reader for that.
--      This config should contain attempts count for each `unGen` (including those in combinators)
--      Current `unGen` should be renamed to `unGen1` and not be exported.
--      Current `unGenTryN` should be changed returning `LazyList (a, g)` and
--      new `unGen` should be implemented trying `retry` times from config using this (`g` must be stored to restore correct state of seed).

---------------------------------------
--- Standard combination interfaces ---
---------------------------------------

Functor RawGen where
  map f $ MkRawGen sf = MkRawGen $ f <$> sf

Applicative RawGen where
  pure x = MkRawGen $ pure x
  MkRawGen x <*> MkRawGen y = MkRawGen $ x <*> y

export
Functor Gen1 where
  map f $ Pure x   = Pure $ f x
  map f $ Raw sf   = Raw $ f <$> sf
  map f $ OneOf oo = mapOneOf oo $ assert_total $ map f
  map f $ Bind x g = Bind x $ assert_total map f . g

export
Applicative Gen1 where
  pure = Pure

  Pure f <*> g = f <$> g
  g <*> Pure x = g <&> \f => f x

  Raw sfl <*> Raw sfr = Raw $ sfl <*> sfr

  OneOf oo <*> g = mapOneOf oo $ assert_total (<*> g)
  g <*> OneOf oo = mapOneOf oo $ assert_total (g <*>)

  Bind x f <*> g = Bind x $ assert_total (<*> g) . f
  g <*> Bind x f = Bind x $ assert_total (g <*>) . f

export
Monad Gen1 where
  Pure x   >>= nf = nf x
  Raw g    >>= nf = Bind g nf -- Raw $ MkRawGen $ sf >>= unGen . nf
  OneOf oo >>= nf = mapOneOf oo $ assert_total (>>= nf)
  Bind x f >>= nf = Bind x $ \x => f x >>= nf

-----------------------------------------
--- Detour: special list of lazy gens ---
-----------------------------------------

namespace GenAlternatives

  export
  record GenAlternatives' (0 mustBeNotEmpty : Bool) a where
    constructor MkGenAlternatives
    unGenAlternatives : LazyLst mustBeNotEmpty (PosNat, Lazy (Gen1 a))

  public export %inline
  GenAlternatives : Type -> Type
  GenAlternatives = GenAlternatives' True

  export %inline
  Nil : GenAlternatives' False a
  Nil = MkGenAlternatives []

  export %inline
  (::) : (0 _ : True `IfUnsolved` e) => Lazy (Gen1 a) -> Lazy (GenAlternatives' e a) -> GenAlternatives' ne a
  x :: xs = MkGenAlternatives $ (1, x) :: xs.unGenAlternatives

  -- This concatenation breaks relative proportions in frequences of given alternative lists
  public export %inline
  (++) : GenAlternatives' nel a -> Lazy (GenAlternatives' ner a) -> GenAlternatives' (nel || ner) a
  xs ++ ys = MkGenAlternatives $ xs.unGenAlternatives ++ ys.unGenAlternatives

  public export %inline
  length : GenAlternatives' ne a -> Nat
  length $ MkGenAlternatives alts = length alts

  export %inline
  processAlternatives : (Gen1 a -> Gen1 b) -> GenAlternatives' ne a -> GenAlternatives' ne b
  processAlternatives f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapSnd (wrapLazy f)

  export %inline
  processAlternativesMaybe : (Gen1 a -> Maybe $ Lazy (Gen1 b)) -> GenAlternatives' ne a -> GenAlternatives' False b
  processAlternativesMaybe f $ MkGenAlternatives xs = MkGenAlternatives $ mapMaybe filt xs where
    %inline filt : (tag, Lazy (Gen1 a)) -> Maybe (tag, Lazy (Gen1 b))
    filt (t, x) = (t,) <$> f x

  export %inline
  processAlternatives'' : (Gen1 a -> GenAlternatives' neb b) -> GenAlternatives' nea a -> GenAlternatives' (nea && neb) b
  processAlternatives'' f = mapGens where

    mapWeight : forall a, nea. (PosNat -> PosNat) -> GenAlternatives' nea a -> GenAlternatives' nea a
    mapWeight f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapFst f

    mapGens : GenAlternatives' nea a -> GenAlternatives' (nea && neb) b
    mapGens $ MkGenAlternatives xs = MkGenAlternatives $ xs `bind` \(w, x) => unGenAlternatives $ mapWeight (w *) $ f x

  export %inline
  processAlternatives' : (Gen1 a -> GenAlternatives' ne b) -> GenAlternatives' ne a -> GenAlternatives' ne b
  processAlternatives' f xs = rewrite sym $ andSameNeutral ne in processAlternatives'' f xs

  export %inline
  relax : GenAlternatives a -> GenAlternatives' ne a
  relax $ MkGenAlternatives alts = MkGenAlternatives $ relaxT alts

  export %inline
  strengthen : GenAlternatives' ne a -> Maybe $ GenAlternatives a
  strengthen $ MkGenAlternatives xs = MkGenAlternatives <$> strengthen xs

export
Cast (LazyLst ne a) (GenAlternatives' ne a) where
  cast = MkGenAlternatives . map (\x => (1, pure x))

public export %inline
altsFromList : LazyLst ne a -> GenAlternatives' ne a
altsFromList = cast

----------------------------------
--- Creation of new generators ---
----------------------------------

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export
oneOf : {default Nothing description : Maybe String} -> GenAlternatives a -> Gen1 a
oneOf $ MkGenAlternatives xs = OneOf $ MkOneOf description xs $ Val _

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : {default Nothing description : Maybe String} -> LazyLst1 (PosNat, Lazy (Gen1 a)) -> Gen1 a
frequency = oneOf {description} . MkGenAlternatives

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : {default Nothing description : Maybe String} -> LazyLst1 a -> Gen1 a
elements = oneOf {description} . cast

------------------------------
--- Analysis of generators ---
------------------------------

export
alternativesOf : Gen1 a -> GenAlternatives a
alternativesOf $ OneOf oo = MkGenAlternatives oo.gens
alternativesOf g          = [g]

||| Any depth alternatives fetching.
|||
||| Alternatives of depth `0` are meant to be a single-item alternatives list with the original generator,
||| alternatives of depth `1` are those returned by the `alternativesOf` function,
||| alternatives of depth `n+1` are alternatives of all alternatives of depth `n` being flattened into a single alternatives list.
export
deepAlternativesOf : (depth : Nat) -> Gen1 a -> GenAlternatives a
deepAlternativesOf 0     gen   = [ gen ]
deepAlternativesOf 1     gen   = alternativesOf gen
deepAlternativesOf (S k) gen   = processAlternatives' alternativesOf $ deepAlternativesOf k gen

||| Returns generator with internal structure hidden (say, revealed by `alternativesOf`),
||| except for empty generator, which would still be returned as empty generator.
export
forgetStructure : Gen1 a -> Gen1 a
forgetStructure g@(Raw _) = g
forgetStructure g = Raw $ MkRawGen $ unGen g

public export
processAlternatives : (Gen1 a -> Gen1 b) -> Gen1 a -> GenAlternatives b
processAlternatives f = processAlternatives f . alternativesOf

public export
mapAlternativesOf : (a -> b) -> Gen1 a -> GenAlternatives b
mapAlternativesOf = processAlternatives . map

public export %inline
mapAlternativesWith : Gen1 a -> (a -> b) -> GenAlternatives b
mapAlternativesWith = flip mapAlternativesOf

-- Priority is chosen to be able to use these operators without parenthesis
-- in expressions of lists, i.e. involving operators `::` and `++`.
infix 8 `mapAlternativesOf`
      , `mapAlternativesWith`

-----------------------------------------------------
--- Detour: implementations for list of lazy gens ---
-----------------------------------------------------

export
Functor (GenAlternatives' ne) where
  map = processAlternatives . map

export
Applicative (GenAlternatives' ne) where
  pure x = [ pure x ]
  xs <*> ys = flip processAlternatives' xs $ flip processAlternatives ys . (<*>)

export
Alternative (GenAlternatives' False) where
  empty = []
  MkGenAlternatives xs <|> MkGenAlternatives ys = MkGenAlternatives $ xs <|> ys

export
Monad (GenAlternatives' True) where
 xs >>= f = flip processAlternatives' xs $ alternativesOf . (>>= oneOf . f)

-------------------------------
--- Variation in generation ---
-------------------------------

-- TODO to reimplement `variant` to ensure that preserves the structure as far as it can.
export
variant : Nat -> Gen1 a -> Gen1 a
variant Z       gen = gen
variant x@(S _) gen = Raw $ MkRawGen $ iterate x independent $ unGen gen where
  iterate : forall a. Nat -> (a -> a) -> a -> a
  iterate Z     _ x = x
  iterate (S n) f x = iterate n f $ f x

-----------------------------
--- Particular generators ---
-----------------------------

export
listOf : {default (choose (0, 10)) length : Gen1 Nat} -> Gen1 a -> Gen1 (List a)
listOf g = sequence $ List.replicate !length g

export
vectOf : {n : Nat} -> Gen1 a -> Gen1 (Vect n a)
vectOf g = sequence $ replicate n g
