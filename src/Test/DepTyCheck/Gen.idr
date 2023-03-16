module Test.DepTyCheck.Gen

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
import public Data.CheckedEmpty.List.Lazy
import Data.Vect
import Data.Stream

import Decidable.Equality

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

  Empty : Gen CanBeEmptyStatic a

  Pure  : a -> Gen em a

  Raw   : RawGen a -> Gen em a

  OneOf : {em : _} -> {alem : _} ->
          alem `NoWeaker` em =>
          NotImmediatelyEmpty alem =>
          OneOfAlternatives alem a -> Gen em a

  Bind  : {em : _} -> {biem : _} ->
          BindToOuter biem em =>
          RawGen c -> (c -> Gen biem a) -> Gen em a

record OneOfAlternatives (0 em : Emptiness) (0 a : Type) where
  constructor MkOneOf
  desc : Maybe String
  totalWeight : PosNat
  gens : LazyLst1 (PosNat, Lazy (Gen em a))
  {auto 0 weightCorrect : totalWeight = foldl1 (+) (gens <&> \x => fst x)}

public export %inline
Gen1 : Type -> Type
Gen1 = Gen NonEmpty

||| Generator with least guaranteed on emptiness.
|||
||| This type should not be used as an input argument unless it is strictly required.
||| You should prefer to be polymorphic on emptiness instead.
public export %inline
Gen0 : Type -> Type
Gen0 = Gen CanBeEmptyStatic

----------------------------
--- Equivalence relation ---
----------------------------

data AltsEquiv : LazyLst lne (PosNat, Lazy (Gen lem a)) -> LazyLst rne (PosNat, Lazy (Gen lem a)) -> Type

export
data Equiv : Gen lem a -> Gen rem a -> Type where
  EE : Empty `Equiv` Empty
  EP : Pure x `Equiv` Pure x
  ER : Raw x `Equiv` Raw x
  EO : lgs `AltsEquiv` rgs => OneOf @{lalemem} @{lalemcd} (MkOneOf _ _ lgs) `Equiv` OneOf @{ralemem} @{ralemcd} (MkOneOf _ _ rgs)
  EB : Bind @{lbo} x g `Equiv` Bind @{rbo} x g

data AltsEquiv : LazyLst lne (PosNat, Lazy (Gen lem a)) -> LazyLst rne (PosNat, Lazy (Gen lem a)) -> Type where
  Nil  : [] `AltsEquiv` []
  (::) : lg `Equiv` rg -> lgs `AltsEquiv` rgs -> {0 lne, rne : _} ->
         {0 lim, rim : _} ->
         {0 lprf, rprf : _} ->
         ((Element n lprf, Delay lg)::lgs) {ne=lne} @{lim} `AltsEquiv` ((Element n prpf, Delay rg)::rgs) {ne=rne} @{rim}

--reflAltsEquiv : (xs : LazyLst ne (PosNat, Lazy (Gen em a))) -> AltsEquiv xs xs
--reflAltsEquiv []      = []
--reflAltsEquiv $ (::) (Element a b, Delay g) (Delay xs) {ne} =
--    (?foo :: reflAltsEquiv xs) {lprf=b} {rprf=b} {lg=g} {rg=g} {lne=ne} {rne=ne} {lim = %search} {rim = %search}

------------------------------------------------
--- Technical stuff for mapping alternatives ---
------------------------------------------------

mapTaggedLazy : (a -> b) -> LazyLst ne (tag, Lazy a) -> LazyLst ne (tag, Lazy b)
mapTaggedLazy = map . mapSnd . wrapLazy

mapOneOf : OneOfAlternatives iem a -> (Gen iem a -> Gen em b) -> OneOfAlternatives em b
mapOneOf (MkOneOf desc tw gs @{prf}) f = MkOneOf desc tw (mapTaggedLazy f gs) @{do
    rewrite mapFusion (Builtin.fst) (mapSnd $ wrapLazy f) gs
    rewrite prf
    cong (Lazy.foldl1 (+)) $ mapExt gs $ \(_, _) => Refl
  }

traverseMaybe : (a -> Maybe b) -> LazyLst ne a -> Maybe $ LazyLst ne b
traverseMaybe f []      = Just []
traverseMaybe f (x::xs) = case f x of
  Nothing => Nothing
  Just y  => (y ::) <$> traverseMaybe f xs

trMTaggedLazy : (a -> Maybe b) -> LazyLst1 (tag, Lazy a) -> Maybe $ LazyLst1 (tag, Lazy b)
trMTaggedLazy = traverseMaybe . m . wrapLazy where
  m : (Lazy a -> Lazy (Maybe b)) -> (tag, Lazy a) -> Maybe (tag, (Lazy b))
  m f (tg, lz) = (tg,) . delay <$> f lz

-- TODO to make the proof properly
trMOneOf : OneOfAlternatives iem a -> (Gen iem a -> Maybe $ Gen em b) -> Maybe $ OneOfAlternatives em b
trMOneOf (MkOneOf desc tw gs @{prf}) f with (trMTaggedLazy f gs) proof trm
  _ | Nothing = Nothing
  _ | Just gs' = Just $ MkOneOf desc tw gs' @{believe_me $ Refl {x=Z}}

-----------------------------
--- Emptiness tweakenings ---
-----------------------------

--export
--relax' : {em : _} -> iem `NoWeaker` em => (original : Gen iem a) -> (relaxed : Gen em a ** relaxed `Equiv` original)
--relax' @{AS} Empty          = (Empty ** EE)
--relax' $ Pure x             = (Pure x ** EP)
--relax' $ Raw x              = (Raw x ** ER)
--relax' $ OneOf @{wo} x@(MkOneOf _ _ _)      = (OneOf @{transitive' wo %search} x ** EO)
--relax' $ Bind @{bo} x f     = Bind @{bindToOuterRelax bo %search} x f

export
relax : {em : _} -> iem `NoWeaker` em => Gen iem a -> Gen em a
relax @{AS} Empty      = Empty
relax $ Pure x         = Pure x
relax $ Raw x          = Raw x
relax $ OneOf @{wo} x  = OneOf @{transitive' wo %search} x
relax $ Bind @{bo} x f = Bind @{bindToOuterRelax bo %search} x f

%transform "relax identity" relax x = believe_me x

-- strengthen' : {em : _} -> (gw : Gen iem a) -> Dec (gs : Gen em a ** gs `Equiv` gw)

export
strengthen : {em : _} -> Gen iem a -> Maybe $ Gen em a

strengthen {em=CanBeEmptyStatic} Empty = Just Empty
strengthen {em=_}                Empty = Nothing

strengthen $ Pure x = Just $ Pure x
strengthen $ Raw x  = Just $ Raw x

strengthen $ OneOf @{_} @{au} x with (decCanBeEmpty em)
  _ | Yes _ = Just $ OneOf @{relaxAnyCanBeEmpty au} @{au} x
  _ | No  _ = map OneOf $ trMOneOf x $ assert_total $ strengthen {em=NonEmpty}

strengthen $ Bind {biem} x f with (decCanBeEmpty em)
  _ | Yes _ = Just $ Bind x f
  _ | No  _ = case biem of
    NonEmpty => Just $ Bind x f
    _        => Nothing

-----------------------------
--- Very basic generators ---
-----------------------------

export
chooseAny : Random a => (0 _ : IfUnsolved ne NonEmpty) => Gen ne a
chooseAny = Raw $ MkRawGen getRandom

export
choose : Random a => (0 _ : IfUnsolved ne NonEmpty) => (a, a) -> Gen ne a
choose bounds = Raw $ MkRawGen $ getRandomR bounds

export
empty : Gen0 a
empty = Empty

--------------------------
--- Running generators ---
--------------------------

--- Non-empty generators ---

export
unGen1 : MonadRandom m => Gen1 a -> m a
unGen1 $ Pure x         = pure x
unGen1 $ Raw sf         = sf.unRawGen
unGen1 $ OneOf @{NN} oo = assert_total unGen1 . force . pickWeighted oo.gens . finToNat =<< randomFin oo.totalWeight
unGen1 $ Bind @{bo} x f = case extractNE bo of Refl => x.unRawGen >>= unGen1 . f

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
unGen $ OneOf oo = assert_total unGen . force . pickWeighted oo.gens . finToNat =<< randomFin oo.totalWeight
unGen $ Bind x f = x.unRawGen >>= unGen . f

export %inline
unGen' : MonadRandom m => Gen em a -> m $ Maybe a
unGen' = runMaybeT . unGen {m=MaybeT m}

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
  map f $ OneOf oo = OneOf $ mapOneOf oo $ assert_total $ map f
  map f $ Bind x g = Bind x $ assert_total map f . g

ap : {em : _} ->
     lem `NoWeaker` em =>
     rem `NoWeaker` em =>
     Gen lem (a -> b) -> Gen rem a -> Gen em b

ap @{AS}      Empty _ = Empty
ap @{_} @{AS} _ Empty = Empty

ap (Pure f) g = relax $ f <$> g
ap g (Pure x) = relax $ g <&> \f => f x

ap (Raw sfl) (Raw sfr) = Raw $ sfl <*> sfr

ap {em=NonEmpty} @{NN} @{NN} (OneOf @{ao} oo) g with (ao) _ | NN = OneOf @{NN} $ mapOneOf oo $ \x => assert_total ap x g
ap {em=CanBeEmptyDynamic} (OneOf oo) g = OneOf @{DD} $ mapOneOf oo $ \x => assert_total ap x g
ap {em=CanBeEmptyStatic}  @{_} @{rr} (OneOf @{_} @{au} oo) g = maybe Empty (OneOf @{AS} @{DD}) $
  trMOneOf oo $ \x => strengthen $ assert_total $ ap @{AS} x g

ap {em=NonEmpty} @{NN} @{NN} g (OneOf @{ao} oo) with (ao) _ | NN = OneOf @{NN} $ mapOneOf oo $ assert_total ap g
ap {em=CanBeEmptyDynamic} g (OneOf oo) = OneOf @{DD} $ mapOneOf oo $ assert_total ap g
ap {em=CanBeEmptyStatic} @{ll} g (OneOf @{_} @{au} oo) = maybe Empty (OneOf @{AS} @{DD}) $
  trMOneOf oo $ \x => strengthen $ assert_total $ ap @{AS} g x

ap @{ll}      (Bind @{bo} x f) (Raw y) = Bind @{bindToOuterRelax bo ll} x $ \c => assert_total $ ap @{reflexive} @{reflexive} (f c) (Raw y)
ap @{_} @{rr} (Raw y) (Bind @{bo} x f) = Bind @{bindToOuterRelax bo rr} x $ \c => assert_total $ ap @{reflexive} @{reflexive} (Raw y) (f c)

ap @{ll} @{rr} (Bind @{lbo} x f) (Bind {biem} @{rbo} y g) with (canBeEmpty em)
  _ | Right cb = Bind {biem=CanBeEmptyStatic} [| (x, y) |] $ \(l, r) => assert_total $ ap (f l) (g r)
  ap @{NN} @{NN} (Bind @{lbo} x f) (Bind {biem=_} @{rbo} y g) | Left Refl with (extractNE lbo) | (extractNE rbo)
    _ | Refl | Refl = Bind @{lbo} [| (x, y) |] $ \(l, r) => assert_total $ ap (f l) (g r)

export
{em : _} -> Applicative (Gen em) where
  pure = Pure
  (<*>) = ap

export
{em : _} -> Monad (Gen em) where
  Empty    >>= _  = Empty
  Pure x   >>= nf = nf x
  Raw g    >>= nf = Bind @{reflexive} g nf
  (OneOf @{ao} oo >>= nf) {em=NonEmpty} with (ao) _ | NN = OneOf $ mapOneOf oo $ assert_total (>>= nf)
  (OneOf @{ao} oo >>= nf) {em=CanBeEmptyDynamic} = OneOf $ mapOneOf oo $ assert_total (>>= nf) . relax @{ao}
  (OneOf oo >>= nf) {em=CanBeEmptyStatic} = maybe Empty (OneOf @{AS} @{DD}) $
    trMOneOf oo $ \x => strengthen $ assert_total $ relax x >>= nf
  Bind {biem} x f >>= nf with (order {rel=NoWeaker} biem em)
    _ | Left _  = Bind x $ \x => assert_total $ relax (f x) >>= nf
    _ | Right _ = Bind {biem} x $ \x => assert_total $ relax (f x) >>= relax . nf

-----------------------------------------
--- Detour: special list of lazy gens ---
-----------------------------------------

namespace GenAlternatives

  export
  record GenAlternatives (0 mustBeNotEmpty : Bool) (em : Emptiness) a where
    constructor MkGenAlternatives
    unGenAlternatives : LazyLst mustBeNotEmpty (PosNat, Lazy (Gen em a))

  export %inline
  Nil : GenAlternatives False em a
  Nil = MkGenAlternatives []

  export %inline
  (::) : {em : _} ->
         lem `NoWeaker` em =>
         rem `NoWeaker` em =>
         (0 _ : IfUnsolved e True) =>
         (0 _ : IfUnsolved em NonEmpty) =>
         (0 _ : IfUnsolved lem em) =>
         (0 _ : IfUnsolved rem em) =>
         Lazy (Gen lem a) -> Lazy (GenAlternatives e rem a) -> GenAlternatives ne em a
  x :: xs = MkGenAlternatives $ (1, wrapLazy relax x) :: mapTaggedLazy relax xs.unGenAlternatives

  -- This concatenation breaks relative proportions in frequences of given alternative lists
  public export %inline
  (++) : {em : _} ->
         lem `NoWeaker` em =>
         rem `NoWeaker` em =>
         (0 _ : IfUnsolved lem em) =>
         (0 _ : IfUnsolved rem em) =>
         (0 _ : IfUnsolved nel False) =>
         (0 _ : IfUnsolved ner False) =>
         GenAlternatives nel lem a -> Lazy (GenAlternatives ner rem a) -> GenAlternatives (nel || ner) em a
  xs ++ ys = MkGenAlternatives $ mapTaggedLazy relax xs.unGenAlternatives ++ mapTaggedLazy relax ys.unGenAlternatives

  public export %inline
  length : GenAlternatives ne em a -> Nat
  length $ MkGenAlternatives alts = length alts

  export %inline
  processAlternatives : (Gen em a -> Gen em b) -> GenAlternatives ne em a -> GenAlternatives ne em b
  processAlternatives f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapSnd (wrapLazy f)

  export %inline
  processAlternativesMaybe : (Gen em a -> Maybe $ Lazy (Gen em b)) -> GenAlternatives ne em a -> GenAlternatives False em b
  processAlternativesMaybe f $ MkGenAlternatives xs = MkGenAlternatives $ mapMaybe (\(t, x) => (t,) <$> f x) xs

  export %inline
  processAlternatives'' : (Gen em a -> GenAlternatives neb em b) -> GenAlternatives nea em a -> GenAlternatives (nea && neb) em b
  processAlternatives'' f = mapGens where

    mapWeight : forall a, nea. (PosNat -> PosNat) -> GenAlternatives nea em a -> GenAlternatives nea em a
    mapWeight f $ MkGenAlternatives xs = MkGenAlternatives $ xs <&> mapFst f

    mapGens : GenAlternatives nea em a -> GenAlternatives (nea && neb) em b
    mapGens $ MkGenAlternatives xs = MkGenAlternatives $ xs `bind` \(w, x) => unGenAlternatives $ mapWeight (w *) $ f x

  export %inline
  processAlternatives' : (Gen em a -> GenAlternatives ne em b) -> GenAlternatives ne em a -> GenAlternatives ne em b
  processAlternatives' f xs = rewrite sym $ andSameNeutral ne in processAlternatives'' f xs

  export %inline
  relax : GenAlternatives True em a -> GenAlternatives ne em a
  relax $ MkGenAlternatives alts = MkGenAlternatives $ relaxT alts

  export %inline
  strengthen : GenAlternatives ne em a -> Maybe $ GenAlternatives True em a
  strengthen $ MkGenAlternatives xs = MkGenAlternatives <$> strengthen xs

  export
  Functor (GenAlternatives ne em) where
    map = processAlternatives . map

  export
  {em : _} -> Applicative (GenAlternatives ne em) where
    pure x = [ pure x ]
    xs <*> ys = flip processAlternatives' xs $ flip processAlternatives ys . (<*>)

  export
  {em : _} -> Alternative (GenAlternatives False em) where
    empty = []
    MkGenAlternatives xs <|> MkGenAlternatives ys = MkGenAlternatives $ xs <|> ys

  -- implementation for `Monad` is below --

export
{em : _} -> Cast (LazyLst ne a) (GenAlternatives ne em a) where
  cast = MkGenAlternatives . map (\x => (1, pure x))

public export %inline
altsFromList : {em : _} -> LazyLst ne a -> GenAlternatives ne em a
altsFromList = cast

----------------------------------
--- Creation of new generators ---
----------------------------------

namespace OneOf

  public export
  data AltsNonEmpty : Bool -> Emptiness -> Type where
    NT : AltsNonEmpty True   NonEmpty
    DT : AltsNonEmpty True   CanBeEmptyDynamic
    Sx : AltsNonEmpty altsNe CanBeEmptyStatic

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export
oneOf : {default Nothing description : Maybe String} ->
        {alem : _} -> {em : _} ->
        alem `NoWeaker` em =>
        AltsNonEmpty altsNe em =>
        (0 _ : IfUnsolved alem em) =>
        (0 _ : IfUnsolved altsNe $ em /= CanBeEmptyStatic) =>
        GenAlternatives altsNe alem a -> Gen em a
oneOf {em=NonEmpty} @{NN} @{NT} $ MkGenAlternatives xs = OneOf $ MkOneOf description _ xs
oneOf {em=CanBeEmptyDynamic} @{_} @{DT} x = case x of MkGenAlternatives xs => OneOf $ MkOneOf description _ xs
oneOf {em=CanBeEmptyStatic}             x = case x of MkGenAlternatives xs => do
  let u : Maybe $ LazyLst1 (_, Lazy _) :=
            strengthen $ flip mapMaybe xs $ \wg => (fst wg,) . delay <$> Gen.strengthen {em=CanBeEmptyDynamic} (snd wg)
  maybe Empty (\gs' => OneOf {alem=CanBeEmptyDynamic} $ MkOneOf description _ gs') u

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : {default Nothing description : Maybe String} ->
            {alem : _} -> {em : _} ->
            alem `NoWeaker` em =>
            AltsNonEmpty altsNe em =>
            (0 _ : IfUnsolved alem em) =>
            (0 _ : IfUnsolved altsNe $ em /= CanBeEmptyStatic) =>
            LazyLst altsNe (PosNat, Lazy (Gen alem a)) -> Gen em a
frequency = oneOf {description} . MkGenAlternatives

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : {default Nothing description : Maybe String} ->
           {em : _} ->
           AltsNonEmpty altsNe em =>
           (0 _ : IfUnsolved em NonEmpty) =>
           (0 _ : IfUnsolved altsNe $ em /= CanBeEmptyStatic) =>
           LazyLst altsNe a -> Gen em a
elements = oneOf {alem=NonEmpty} {description} . altsFromList

export %inline
elements' : Foldable f => {default Nothing description : Maybe String} -> f a -> Gen0 a
elements' xs = elements {description} $ relaxF $ fromList $ toList xs

------------------------------
--- Analysis of generators ---
------------------------------

export
alternativesOf : {em : _} -> Gen em a -> GenAlternatives True em a
alternativesOf $ OneOf oo = MkGenAlternatives $ gens $ mapOneOf oo relax
alternativesOf g          = [g]

||| Any depth alternatives fetching.
|||
||| Alternatives of depth `0` are meant to be a single-item alternatives list with the original generator,
||| alternatives of depth `1` are those returned by the `alternativesOf` function,
||| alternatives of depth `n+1` are alternatives of all alternatives of depth `n` being flattened into a single alternatives list.
export
deepAlternativesOf : {em : _} -> (depth : Nat) -> Gen em a -> GenAlternatives True em a
deepAlternativesOf 0     gen = [ gen ]
deepAlternativesOf 1     gen = alternativesOf gen
deepAlternativesOf (S k) gen = processAlternatives' alternativesOf $ deepAlternativesOf k gen

||| Returns generator with internal structure hidden (say, revealed by `alternativesOf`),
||| except for empty generator, which would still be returned as empty generator.
export
forgetStructure : {em : _} -> Gen em a -> Gen em a
forgetStructure Empty               = Empty
forgetStructure g@(Raw _)           = g
forgetStructure g with (canBeEmpty em)
  _ | Right _   = MkRawGen (unGen' g) `Bind` maybe Empty Pure
  _ | Left Refl = Raw $ MkRawGen $ unGen1 g

public export
processAlternatives : {em : _} -> (Gen em a -> Gen em b) -> Gen em a -> GenAlternatives True em b
processAlternatives f = processAlternatives f . alternativesOf

public export
mapAlternativesOf : {em : _} -> (a -> b) -> Gen em a -> GenAlternatives True em b
mapAlternativesOf = processAlternatives . map

public export %inline
mapAlternativesWith : {em : _} -> Gen em a -> (a -> b) -> GenAlternatives True em b
mapAlternativesWith = flip mapAlternativesOf

-- Priority is chosen to be able to use these operators without parenthesis
-- in expressions of lists, i.e. involving operators `::` and `++`.
infix 8 `mapAlternativesOf`
      , `mapAlternativesWith`

export %hint
GenAltsMonad : {em : _} -> em `NoWeaker` CanBeEmptyDynamic => Monad (GenAlternatives True em)
--GenAltsMonad = M where
--  [M] Monad (GenAlternatives True em) where
--    xs >>= f = flip processAlternatives' xs $ alternativesOf . (>>= oneOf . f)

-----------------
--- Filtering ---
-----------------

export
mapMaybe : (a -> Maybe b) -> Gen em a -> Gen0 b
mapMaybe f g = maybe empty pure . f =<< relax g

export
suchThat_withPrf : Gen em a -> (p : a -> Bool) -> Gen0 $ a `Subset` So . p
suchThat_withPrf g p = mapMaybe lp g where
  lp : a -> Maybe $ a `Subset` So . p
  lp x with (p x) proof prf
    lp x | True  = Just $ Element x $ eqToSo prf
    lp x | False = Nothing

infixl 4 `suchThat`

public export
suchThat : Gen em a -> (a -> Bool) -> Gen0 a
suchThat g p = fst <$> suchThat_withPrf g p

export
suchThat_dec : Gen em a -> ((x : a) -> Dec (prop x)) -> Gen0 $ Subset a prop
suchThat_dec g f = mapMaybe d g where
  d : a -> Maybe $ Subset a prop
  d x = case f x of
    Yes p => Just $ Element x p
    No  _ => Nothing

||| Filters the given generator so, that resulting values `x` are solutions of equation `y = f x` for given `f` and `y`.
export
suchThat_invertedEq : DecEq b => Gen em a -> (y : b) -> (f : a -> b) -> Gen0 $ Subset a $ \x => y = f x
suchThat_invertedEq g y f = g `suchThat_dec` \x => y `decEq` f x

-------------------------------
--- Variation in generation ---
-------------------------------

iterate : forall a. Nat -> (a -> a) -> a -> a
iterate Z     _ x = x
iterate (S n) f x = iterate n f $ f x

-- TODO to reimplement `variant` to ensure that preserves the structure as far as it can.
export
variant : {em : _} -> Nat -> Gen em a -> Gen em a
variant _     Empty = Empty
variant Z       gen = gen
variant n gen with (canBeEmpty em)
  _ | Right _   = MkRawGen (iterate n independent $ unGen' gen) `Bind` maybe Empty Pure
  _ | Left Refl = Raw $ MkRawGen $ iterate n independent $ unGen1 gen

-----------------------------
--- Particular generators ---
-----------------------------

export
listOf : {em : _} -> {default (choose (0, 10)) length : Gen em Nat} -> Gen em a -> Gen em (List a)
listOf g = sequence $ List.replicate !length g

export
vectOf : {em : _} -> {n : Nat} -> Gen em a -> Gen em (Vect n a)
vectOf g = sequence $ replicate n g
