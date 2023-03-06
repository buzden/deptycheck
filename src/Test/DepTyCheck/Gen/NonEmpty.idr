module Test.DepTyCheck.Gen.NonEmpty

import Control.Monad.Maybe
import public Control.Monad.Error.Interface
import Control.Monad.Random
import public Control.Monad.Random.Interface
import Control.Monad.State
import public Control.Monad.State.Interface

import Data.Bool
import Data.Fuel
import Data.Nat.Pos
import Data.List
import Data.List.Lazy
import Data.CheckedEmpty.List.Lazy
import Data.Singleton
import Data.Stream
import Data.Vect

import public Language.Implicits.IfUnsolved

import public Test.DepTyCheck.Gen.Emptiness

%default total

-------------------------
--- Utility functions ---
-------------------------

randomFin : MonadRandom m => (n : PosNat) -> m $ Fin $ fst n
randomFin $ Element (S _) _ = getRandom

public export %inline
wrapLazy : (a -> b) -> Lazy a -> Lazy b
wrapLazy f = delay . f . force

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

record RawGen a where
  constructor MkRawGen
  unRawGen : forall m. MonadRandom m => m a

record OneOfAlternatives (0 em : Emptiness) (0 a : Type)

export
data Gen : Emptiness -> Type -> Type where

  Empty : Gen (CanBeEmpty Static) a

  Pure  : (0 _ : IfUnsolved em NonEmpty) =>
          a -> Gen em a

  Raw   : (0 _ : IfUnsolved em NonEmpty) =>
          RawGen a -> Gen em a

  OneOf : AltsToOuter alem em =>
          (0 _ : IfUnsolved em NonEmpty) =>
          OneOfAlternatives alem a -> Gen em a

  Bind  : BindToOuter biem em =>
          (0 _ : IfUnsolved em NonEmpty) =>
          RawGen c -> (c -> Gen biem a) -> Gen em a

record OneOfAlternatives (0 em : Emptiness) (0 a : Type) where
  constructor MkOneOf
  desc : Maybe String
  totalWeight : PosNat
  gens : LazyLst1 (PosNat, Lazy (Gen em a))
  {auto 0 weightCorrect : totalWeight = foldl1 (+) (gens <&> \x => fst x)}

-- TODO To think about arbitrary discrete final probability distribution instead of only uniform.

public export %inline
Gen1 : Type -> Type
Gen1 = Gen NonEmpty

------------------------------------------------
--- Technical stuff for mapping alternatives ---
------------------------------------------------

mapTaggedLazy : (a -> b) -> LazyLst1 (tag, Lazy a) -> LazyLst1 (tag, Lazy b)
mapTaggedLazy = map . mapSnd . wrapLazy

mapOneOf' : OneOfAlternatives iem a -> (Gen iem a -> Gen em b) -> OneOfAlternatives em b
mapOneOf' (MkOneOf desc tw gs @{prf}) f = MkOneOf desc tw (mapTaggedLazy f gs) @{do
    rewrite mapFusion (Builtin.fst) (mapSnd $ wrapLazy f) gs
    transport tw $ cong (Lazy.foldl1 (+)) $ mapExt gs $ \(_, _) => Refl

--%inline
--mapOneOf : em `NoWeaker` CanBeEmpty Dynamic => OneOfAlternatives iem a -> (Gen iem a -> Gen em b) -> Gen em b
--mapOneOf = OneOf @{altsToOuterRefl} .: mapOneOf'

-----------------------------
--- Emptiness tweakenings ---
-----------------------------

export
relax : iem `NoWeaker` oem => Gen iem a -> Gen oem a
relax @{Refl} x        = x
relax $ Pure x         = Pure x
relax $ Raw x          = Raw x
relax $ OneOf @{ao} x  = OneOf @{altsToOuterRelax ao %search} x
relax $ Bind @{bo} x f = Bind @{bindToOuterRelax bo %search} x f

%transform "relax identity" relax x = believe_me x

export
strengthen : oem `NoWeaker` iem => Gen iem a -> Maybe $ Gen oem a
strengthen        $ Pure x                                    = Just $ Pure x
strengthen        $ Raw x                                     = Just $ Raw x
strengthen @{Refl}  x                                         = Just x
strengthen @{NED} $ OneOf @{AltsEE {dp=Dynamic}} x            = Nothing
strengthen @{NED} $ OneOf @{AltsNE {em=CanBeEmpty Dynamic}} x = Just $ OneOf x
strengthen @{NED} $ OneOf @{AltsEE {dp=Static}} x             impossible
strengthen @{NED} $ OneOf @{AltsNE {em=NonEmpty}} x           impossible
strengthen @{NED} $ OneOf @{AltsNE {em=CanBeEmpty Static}} x  impossible
strengthen @{NED} $ Bind @{BndNE} x f                         = Just $ Bind x f
strengthen @{NED} $ Bind @{BndEE} x f                         = Nothing
strengthen @{NES}   Empty                                     = Nothing
strengthen @{NES} $ OneOf @{AltsEE {dp=Static}} x             = Nothing
strengthen @{NES} $ OneOf @{AltsNE {em=CanBeEmpty Static}} x  = Just $ OneOf x
strengthen @{NES} $ OneOf @{AltsEE {dp=Dynamic}} x            impossible
strengthen @{NES} $ OneOf @{AltsNE {em=NonEmpty}} x           impossible
strengthen @{NES} $ OneOf @{AltsNE {em=CanBeEmpty Dynamic}} x impossible
strengthen @{NES} $ Bind @{BndNE} x f                         = Just $ Bind x f
strengthen @{NES} $ Bind @{BndEE} x f                         = Nothing
strengthen @{EDS}   Empty                                     = Nothing
strengthen @{EDS} $ OneOf @{AltsEE {dp=Static}} x             = Just $ OneOf x
strengthen @{EDS} $ OneOf @{AltsNE {em=CanBeEmpty Static}} x  = Just $ OneOf x
strengthen @{EDS} $ OneOf @{AltsEE {dp=Dynamic}} x            impossible
strengthen @{EDS} $ OneOf @{AltsNE {em=NonEmpty}} x           impossible
strengthen @{EDS} $ OneOf @{AltsNE {em=CanBeEmpty Dynamic}} x impossible
strengthen @{EDS} $ Bind @{BndNE} x f                         = Just $ Bind x f
strengthen @{EDS} $ Bind @{BndEE} x f                         = Just $ Bind x f

-----------------------------
--- Very basic generators ---
-----------------------------

export
chooseAny : Random a => (0 _ : IfUnsolved ne NonEmpty) => Gen ne a
chooseAny = Raw $ MkRawGen getRandom

export
choose : Random a => (0 _ : IfUnsolved ne NonEmpty) => (a, a) -> Gen ne a
choose bounds = Raw $ MkRawGen $ getRandomR bounds

--------------------------
--- Running generators ---
--------------------------

--- Non-empty generators ---

export
unGen1 : MonadRandom m => Gen1 a -> m a
unGen1 $ Pure x             = pure x
unGen1 $ Raw sf             = sf.unRawGen
unGen1 $ OneOf @{AltsNE} oo = assert_total unGen1 . force . pickWeighted oo.gens . finToNat =<< randomFin oo.totalWeight
unGen1 $ Bind @{BndNE} x f  = x.unRawGen >>= unGen1 . f

export
unGenAll' : RandomGen g => (seed : g) -> Gen1 a -> Stream (g, a)
unGenAll' seed gen = do
  let sv@(seed, _) = runRandom seed $ unGen1 {m=Rand} gen
  sv :: unGenAll' seed gen

export
unGenAll : RandomGen g => (seed : g) -> Gen1 a -> Stream a
unGenAll = map snd .: unGenAll'

--- Possibly empty generators ---

export
unGen : MonadRandom m => MonadError () m => Gen em a -> m a
unGen $ Empty    = throwError ()
unGen $ Pure x   = pure x
unGen $ Raw sf   = sf.unRawGen
unGen $ OneOf oo = assert_total unGen . force . pickWeighted oo.gens . finToNat =<< randomFin oo.totalWeight.unVal
unGen $ Bind x f = x.unRawGen >>= unGen . f

export
unGenTryAll' : RandomGen g => (seed : g) -> Gen em a -> Stream (g, Maybe a)
unGenTryAll' seed gen = do
  let sv@(seed, _) = runRandom seed $ runMaybeT $ unGen {m=MaybeT Rand} gen
  sv :: unGenTryAll' seed gen

export
unGenTryAll : RandomGen g => (seed : g) -> Gen em a -> Stream $ Maybe a
unGenTryAll = map snd .: unGenTryAll'

export
unGenTryN : RandomGen g => (n : Nat) -> g -> Gen em a -> LazyList a
unGenTryN n = mapMaybe id .: take (limit n) .: unGenTryAll

-- TODO To add config and Reader for that.
--      This config should contain attempts count for each `unGen` (including those in combinators)
--      Current `unGen` should be renamed to `unGen1` and not be exported.
--      Current `unGenTryN` should be changed returning `LazyList (a, g)` and
--      new `unGen` should be implemented trying `retry` times from config using this (`g` must be stored to restore correct state of seed).

---------------------------------------
--- Standard combination interfaces ---
---------------------------------------

--- `RawGen` ---

Functor RawGen where
  map f $ MkRawGen sf = MkRawGen $ f <$> sf

Applicative RawGen where
  pure x = MkRawGen $ pure x
  MkRawGen x <*> MkRawGen y = MkRawGen $ x <*> y

--- `Gen` ---

export
Functor (Gen em) where
  map f $ Empty    = Empty
  map f $ Pure x   = Pure $ f x
  map f $ Raw sf   = Raw $ f <$> sf
  map f $ OneOf oo = OneOf $ mapOneOf' oo $ assert_total $ map f
  map f $ Bind x g = Bind x $ assert_total map f . g

ap : lem `NoWeaker` em => rem `NoWeaker` em =>
     Gen lem (a -> b) -> Gen rem a -> Gen em b
ap @{Refl} Empty _ = Empty
ap @{_} @{Refl} _ Empty = Empty

ap (Pure f) g = relax $ f <$> g
ap g (Pure x) = relax $ g <&> \f => f x

ap (Raw sfl) (Raw sfr) = Raw $ sfl <*> sfr

ap @{Refl} @{Refl} (OneOf @{ao} oo) g = OneOf @{?foo} $ mapOneOf' oo $ \x => assert_total $ ap x g @{altsToOuterRelax' ao} @{Refl}
ap @{Refl} @{NED}  (OneOf @{ao} oo) g = ?foo_5
ap @{Refl} @{NES}  (OneOf @{ao} oo) g = ?foo_6
ap @{Refl} @{EDS}  (OneOf @{ao} oo) g = ?foo_7
ap @{NED}  @{rbo}  (OneOf @{ao} oo) g = ?foo_1
ap @{NES}  @{rbo}  (OneOf @{ao} oo) g = ?foo_2
ap @{EDS}  @{rbo}  (OneOf @{ao} oo) g = ?foo_3
--ap @{Refl} (OneOf @{bo} oo) g = OneOf @{?foooo0} $ mapOneOf' oo $ assert_total $ \x => ap x g @{?safd0} @{?foo0}
--ap @{NED}  (OneOf @{bo} oo) g = OneOf @{?foooo1} $ mapOneOf' oo $ assert_total $ \x => ap x g @{?safd1} @{?foo1}
--ap @{NES}  (OneOf @{bo} oo) g = OneOf @{?foooo2} $ mapOneOf' oo $ assert_total $ \x => ap x g @{?safd2} @{?foo2}
--ap @{EDS}  (OneOf @{bo} oo) g = OneOf @{?foooo3} $ mapOneOf' oo $ assert_total $ \x => ap x g @{?safd3} @{?foo3}
ap @{_} @{rbo} g (OneOf @{bo} oo) = ?foo_ap_oneof_r -- mapOneOf @{transitive' bo rbo} oo $ assert_total (g `ap`)

ap @{lbo} @{rbo} (Bind @{bo} x f) g = ?foo_bnd_l -- Bind @{bindToOuterRelax bo lbo} x $ \y => ap @{?foo_nw} @{?foo_nw2} (f y) $ relax @{?foo_f} g
ap g (Bind x f) = ?foo_bnd_r -- Bind x $ ?foo_bnd_r -- assert_total (g `ap`) . f

export
Applicative (Gen em) where
  pure = Pure
  (<*>) = ap @{?foo_l} @{?foo_r}

{-

export
Monad Gen where
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
    unGenAlternatives : LazyLst mustBeNotEmpty (PosNat, Lazy (Gen a))

  public export %inline
  GenAlternatives : Type -> Type
  GenAlternatives = GenAlternatives' True

  export %inline
  Nil : GenAlternatives' False a
  Nil = MkGenAlternatives []

  export %inline
  (::) : (0 _ : True `IfUnsolved` e) => Lazy (Gen a) -> Lazy (GenAlternatives' e a) -> GenAlternatives' ne a
  x :: xs = MkGenAlternatives $ (1, x) :: xs.unGenAlternatives

  -- This concatenation breaks relative proportions in frequences of given alternative lists
  public export %inline
  (++) : GenAlternatives' nel a -> Lazy (GenAlternatives' ner a) -> GenAlternatives' (nel || ner) a
  xs ++ ys = MkGenAlternatives $ xs.unGenAlternatives ++ ys.unGenAlternatives

  public export %inline
  length : GenAlternatives' ne a -> Nat
  length $ MkGenAlternatives alts = length alts

  export %inline
  processAlternatives : (Gen a -> Gen b) -> GenAlternatives' ne a -> GenAlternatives' ne b
  processAlternatives f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapSnd (wrapLazy f)

  export %inline
  processAlternativesMaybe : (Gen a -> Maybe $ Lazy (Gen b)) -> GenAlternatives' ne a -> GenAlternatives' False b
  processAlternativesMaybe f $ MkGenAlternatives xs = MkGenAlternatives $ mapMaybe filt xs where
    %inline filt : (tag, Lazy (Gen a)) -> Maybe (tag, Lazy (Gen b))
    filt (t, x) = (t,) <$> f x

  export %inline
  processAlternatives'' : (Gen a -> GenAlternatives' neb b) -> GenAlternatives' nea a -> GenAlternatives' (nea && neb) b
  processAlternatives'' f = mapGens where

    mapWeight : forall a, nea. (PosNat -> PosNat) -> GenAlternatives' nea a -> GenAlternatives' nea a
    mapWeight f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapFst f

    mapGens : GenAlternatives' nea a -> GenAlternatives' (nea && neb) b
    mapGens $ MkGenAlternatives xs = MkGenAlternatives $ xs `bind` \(w, x) => unGenAlternatives $ mapWeight (w *) $ f x

  export %inline
  processAlternatives' : (Gen a -> GenAlternatives' ne b) -> GenAlternatives' ne a -> GenAlternatives' ne b
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
oneOf : {default Nothing description : Maybe String} -> GenAlternatives a -> Gen a
oneOf $ MkGenAlternatives xs = OneOf $ MkOneOf description _ xs

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : {default Nothing description : Maybe String} -> LazyLst1 (PosNat, Lazy (Gen a)) -> Gen a
frequency = oneOf {description} . MkGenAlternatives

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : {default Nothing description : Maybe String} -> LazyLst1 a -> Gen a
elements = oneOf {description} . cast

------------------------------
--- Analysis of generators ---
------------------------------

export
alternativesOf : Gen a -> GenAlternatives a
alternativesOf $ OneOf oo = MkGenAlternatives oo.gens
alternativesOf g          = [g]

||| Any depth alternatives fetching.
|||
||| Alternatives of depth `0` are meant to be a single-item alternatives list with the original generator,
||| alternatives of depth `1` are those returned by the `alternativesOf` function,
||| alternatives of depth `n+1` are alternatives of all alternatives of depth `n` being flattened into a single alternatives list.
export
deepAlternativesOf : (depth : Nat) -> Gen a -> GenAlternatives a
deepAlternativesOf 0     gen   = [ gen ]
deepAlternativesOf 1     gen   = alternativesOf gen
deepAlternativesOf (S k) gen   = processAlternatives' alternativesOf $ deepAlternativesOf k gen

||| Returns generator with internal structure hidden (say, revealed by `alternativesOf`),
||| except for empty generator, which would still be returned as empty generator.
export
forgetStructure : Gen a -> Gen a
forgetStructure g@(Raw _) = g
forgetStructure g = Raw $ MkRawGen $ unGen g

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
variant : Nat -> Gen a -> Gen a
variant Z       gen = gen
variant x@(S _) gen = Raw $ MkRawGen $ iterate x independent $ unGen gen where
  iterate : forall a. Nat -> (a -> a) -> a -> a
  iterate Z     _ x = x
  iterate (S n) f x = iterate n f $ f x

-----------------------------
--- Particular generators ---
-----------------------------

export
listOf : {default (choose (0, 10)) length : Gen Nat} -> Gen a -> Gen (List a)
listOf g = sequence $ List.replicate !length g

export
vectOf : {n : Nat} -> Gen a -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
