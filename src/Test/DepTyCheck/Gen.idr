module Test.DepTyCheck.Gen

import Control.Monad.Maybe
import public Control.Monad.Error.Interface
import Control.Monad.Random
import public Control.Monad.Random.Interface
import Control.Monad.State
import public Control.Monad.State.Interface

import Data.Bool
import public Data.CheckedEmpty.List.Lazy
import Data.Fuel
import public Data.Nat1
import Data.List
import Data.List.Lazy
import Data.List.Lazy.Extra
import Data.Singleton
import Data.SnocList
import Data.Stream
import Data.Vect

import Decidable.Equality

import public Language.Implicits.IfUnsolved

import Syntax.WithProof

import public Test.DepTyCheck.Gen.Emptiness
import public Test.DepTyCheck.Gen.Labels

%default total

%hide Singleton.(<*>)

-------------------------
--- Utility functions ---
-------------------------

randomFin : MonadRandom m => (n : Nat1) -> m $ Fin n.asNat
randomFin $ FromNat (S _) = getRandom

public export %inline
wrapLazy : (a -> b) -> Lazy a -> Lazy b
wrapLazy f = delay . f . force

transport : Singleton x -> x = y -> Singleton y
transport z Refl = z

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

record RawGen a where
  constructor MkRawGen
  unRawGen : forall m. MonadRandom m => CanManageLabels m => m a

export
record GenAlternatives (0 mustBeNotEmpty : Bool) (em : Emptiness) (a : Type)

export
data Gen : Emptiness -> Type -> Type where

  Empty : Gen MaybeEmpty a

  Pure  : a -> Gen em a

  Raw   : RawGen a -> Gen em a

  OneOf : alem `NoWeaker` em =>
          NotImmediatelyEmpty alem =>
          GenAlternatives True alem a -> Gen em a

  Bind  : {biem : _} ->
          (0 _ : BindToOuter biem em) =>
          RawGen c -> (c -> Gen biem a) -> Gen em a

  Labelled : Label -> Gen em a -> Gen em a

record GenAlternatives (0 mustBeNotEmpty : Bool) (em : Emptiness) (a : Type) where
  constructor MkGenAlts
  unGenAlts : LazyLst mustBeNotEmpty (Nat1, Lazy (Gen em a))

(.totalWeight) : GenAlternatives True em a -> Nat1
(.totalWeight) oo = foldl1 (+) (oo.unGenAlts <&> \x => fst x)

public export %inline
Gen1 : Type -> Type
Gen1 = Gen NonEmpty

||| Generator with least guarantees on emptiness.
|||
||| This type should not be used as an input argument unless it is strictly required.
||| You should prefer to be polymorphic on emptiness instead.
public export %inline
Gen0 : Type -> Type
Gen0 = Gen MaybeEmpty

-----------------------------
--- Very basic generators ---
-----------------------------

export
chooseAny : Random a => (0 _ : IfUnsolved ne NonEmpty) => Gen ne a
chooseAny = Raw $ MkRawGen getRandom

public export %inline
chooseAnyOf : (0 a : _) -> Random a => (0 _ : IfUnsolved ne NonEmpty) => Gen ne a
chooseAnyOf _ = chooseAny

export
choose : Random a => (0 _ : IfUnsolved ne NonEmpty) => (a, a) -> Gen ne a
choose bounds = Raw $ MkRawGen $ getRandomR bounds

export %inline
empty : Gen0 a
empty = Empty

export
label : Label -> Gen em a -> Gen em a
label _ Empty = Empty
label l g     = Labelled l g

----------------------------
--- Equivalence relation ---
----------------------------

data AltsEquiv : LazyLst lne (Nat1, Lazy (Gen lem a)) -> LazyLst rne (Nat1, Lazy (Gen lem a)) -> Type

export
data Equiv : Gen lem a -> Gen rem a -> Type where
  EE : Empty `Equiv` Empty
  EP : Pure x `Equiv` Pure x
  ER : Raw x `Equiv` Raw x
  EO : lgs `AltsEquiv` rgs => OneOf @{lalemem} @{lalemcd} (MkGenAlts lgs) `Equiv` OneOf @{ralemem} @{ralemcd} (MkGenAlts rgs)
  EB : Bind @{lbo} x g `Equiv` Bind @{rbo} x g

data AltsEquiv : LazyLst lne (Nat1, Lazy (Gen lem a)) -> LazyLst rne (Nat1, Lazy (Gen lem a)) -> Type where
  Nil  : [] `AltsEquiv` []
  (::) : lg `Equiv` rg -> lgs `AltsEquiv` rgs -> {0 lne, rne : _} ->
         {0 lim, rim : _} ->
         {0 lprf, rprf : _} ->
         ((FromNat n @{lprf}, Delay lg)::lgs) {ne=lne} @{lim} `AltsEquiv` ((FromNat n @{prpf}, Delay rg)::rgs) {ne=rne} @{rim}

--reflAltsEquiv : (xs : LazyLst ne (Nat1, Lazy (Gen em a))) -> AltsEquiv xs xs
--reflAltsEquiv []      = []
--reflAltsEquiv $ (::) (Element a b, Delay g) (Delay xs) {ne} =
--    (?foo :: reflAltsEquiv xs) {lprf=b} {rprf=b} {lg=g} {rg=g} {lne=ne} {rne=ne} {lim = %search} {rim = %search}

------------------------------------------------
--- Technical stuff for mapping alternatives ---
------------------------------------------------

mapTaggedLazy : (a -> b) -> LazyLst ne (tag, Lazy a) -> LazyLst ne (tag, Lazy b)
mapTaggedLazy = map . mapSnd . wrapLazy

mapOneOf : GenAlternatives ne iem a -> (Gen iem a -> Gen em b) -> GenAlternatives ne em b
mapOneOf (MkGenAlts gs) f = MkGenAlts $ mapTaggedLazy f gs

traverseMaybe : (a -> Maybe b) -> LazyLst ne a -> Maybe $ LazyLst ne b
traverseMaybe f []      = Just []
traverseMaybe f (x::xs) = case f x of
  Nothing => Nothing
  Just y  => (y ::) <$> traverseMaybe f xs

trMTaggedLazy : (a -> Maybe b) -> LazyLst ne (tag, Lazy a) -> Maybe $ LazyLst ne (tag, Lazy b)
trMTaggedLazy = traverseMaybe . m . wrapLazy where
  m : (Lazy a -> Lazy (Maybe b)) -> (tag, Lazy a) -> Maybe (tag, (Lazy b))
  m f (tg, lz) = (tg,) . delay <$> f lz

trMOneOf : GenAlternatives ne iem a -> (Gen iem a -> Maybe $ Gen em b) -> Maybe $ GenAlternatives ne em b
trMOneOf (MkGenAlts gs) f = MkGenAlts <$> trMTaggedLazy f gs

-----------------------------
--- Emptiness tweakenings ---
-----------------------------

--export
--relax' : {em : _} -> iem `NoWeaker` em => (original : Gen iem a) -> (relaxed : Gen em a ** relaxed `Equiv` original)

export
relax : iem `NoWeaker` em => Gen iem a -> Gen em a
relax @{AS} Empty      = Empty
relax $ Pure x         = Pure x
relax $ Raw x          = Raw x
relax $ OneOf @{wo} x  = OneOf @{transitive' wo %search} x
relax $ Bind @{bo} x f = Bind @{bindToOuterRelax bo %search} x f
relax $ Labelled l x   = label l $ relax x

--export
--strengthen' : {em : _} -> (gw : Gen iem a) -> Dec (gs : Gen em a ** gs `Equiv` gw)

export
strengthen : {em : _} -> Gen iem a -> Maybe $ Gen em a

strengthen {em=MaybeEmpty} Empty = Just Empty
strengthen {em=_}          Empty = Nothing

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

strengthen $ Labelled l x = label l <$> strengthen x

--------------------
--- More utility ---
--------------------

mkOneOf : alem `NoWeaker` em =>
          NotImmediatelyEmpty alem =>
          (gens : LazyLst1 (Nat1, Lazy (Gen alem a))) ->
          Gen em a
mkOneOf gens = OneOf $ MkGenAlts gens
-- TODO to make elimination of a single element

--------------------------
--- Running generators ---
--------------------------

--- Non-empty generators ---

export
unGen1 : MonadRandom m => CanManageLabels m => Gen1 a -> m a
unGen1 $ Pure x         = pure x
unGen1 $ Raw sf         = sf.unRawGen
unGen1 $ OneOf @{NN} oo = assert_total unGen1 . force . pickWeighted oo.unGenAlts . finToNat =<< randomFin oo.totalWeight
unGen1 $ Bind @{bo} x f = case extractNE bo of Refl => x.unRawGen >>= unGen1 . f
unGen1 $ Labelled l x   = manageLabel l $ unGen1 x

export
unGenAll' : RandomGen g => (seed : g) -> Gen1 a -> Stream (g, a)
unGenAll' seed gen = do
  let sv@(seed, _) = runRandom seed $ unGen1 {m=Rand} gen
  sv :: unGenAll' seed gen

export
unGenAll : RandomGen g => (seed : g) -> Gen1 a -> Stream a
unGenAll = map snd .: unGenAll'

||| Picks one random value from a generator
export
pick1 : CanInitSeed g m => Functor m => Gen1 a -> m a
pick1 gen = initSeed <&> \s => evalRandom s $ unGen1 gen

--- Possibly empty generators ---

export
unGen : MonadRandom m => MonadError () m => CanManageLabels m => Gen em a -> m a
unGen $ Empty        = throwError ()
unGen $ Pure x       = pure x
unGen $ Raw sf       = sf.unRawGen
unGen $ OneOf oo     = assert_total unGen . force . pickWeighted oo.unGenAlts . finToNat =<< randomFin oo.totalWeight
unGen $ Bind x f     = x.unRawGen >>= unGen . f
unGen $ Labelled l x = manageLabel l $ unGen x

export %inline
unGen' : MonadRandom m => CanManageLabels m => Gen em a -> m $ Maybe a
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

||| Tries once to pick a random value from a generator
export
pick : CanInitSeed g m => Functor m => Gen em a -> m $ Maybe a
pick gen = initSeed <&> \s => evalRandom s $ unGen' gen

||| Tries to pick a random value from a generator, returning the number of unsuccessful attempts, if generated successfully
export
pickTryN : CanInitSeed g m => Functor m => (n : Nat) -> Gen em a -> m $ Maybe (Fin n, a)
pickTryN n g = initSeed <&> \s => head' (withIndex $ unGenTryN n s g) >>= \(i, x) => natToFin i n <&> (,x)

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
  map f $ Empty        = Empty
  map f $ Pure x       = Pure $ f x
  map f $ Raw sf       = Raw $ f <$> sf
  map f $ OneOf oo     = OneOf $ mapOneOf oo $ assert_total $ map f
  map f $ Bind x g     = Bind x $ assert_total map f . g
  map f $ Labelled l x = label l $ map f x

export
{em : _} -> Applicative (Gen em) where

  pure = Pure

  Empty <*> _ = Empty
  _ <*> Empty = Empty

  Pure f <*> g = f <$> g
  g <*> Pure x = g <&> \f => f x

  Raw sfl <*> Raw sfr = Raw $ sfl <*> sfr

  Labelled l x <*> y = label l $ x <*> y
  x <*> Labelled l y = label l $ x <*> y

  OneOf @{ao} @{au} {alem} oo <*> g = case canBeNotImmediatelyEmpty em of
    Right _   => OneOf {em} $ mapOneOf oo $ \x => assert_total $ relax x <*> g
    Left Refl => maybe Empty (\g => OneOf $ mapOneOf oo $ \x => assert_total $ relax x <*> g) $ strengthen {em=MaybeEmptyDeep} g
  g <*> OneOf oo = case canBeNotImmediatelyEmpty em of
    Right _   => OneOf {em} $ mapOneOf oo $ \x => assert_total $ g <*> relax x
    Left Refl => maybe Empty (\g => OneOf $ mapOneOf oo $ \x => assert_total $ g <*> relax x) $ strengthen {em=MaybeEmptyDeep} g

  Bind x f <*> Raw y = Bind x $ \c => f c <*> Raw y
  Raw y <*> Bind x f = Bind x $ \c => assert_total $ Raw y <*> f c

  Bind {biem=bl} @{lbo} x f <*> Bind {biem=br} @{rbo} y g = case order {rel=NoWeaker} bl br of
    Left  _ => Bind {biem=br} [| (x, y) |] $ \(l, r) => assert_total $ relax (f l) <*> g r
    Right _ => Bind {biem=bl} [| (x, y) |] $ \(l, r) => assert_total $ f l <*> relax (g r)

export
{em : _} -> Monad (Gen em) where
  Empty    >>= _  = Empty
  Pure x   >>= nf = nf x
  Raw g    >>= nf = Bind @{reflexive} g nf
  (OneOf @{ao} oo >>= nf) {em=NonEmpty} with (ao) _ | NN = OneOf $ mapOneOf oo $ assert_total (>>= nf)
  (OneOf @{ao} oo >>= nf) {em=MaybeEmptyDeep} = OneOf $ mapOneOf oo $ assert_total (>>= nf) . relax @{ao}
  (OneOf {alem} (MkGenAlts gs) >>= nf) {em=MaybeEmpty} = maybe Empty (mkOneOf {alem=MaybeEmptyDeep}) $
    strengthen $ flip mapMaybe gs $ traverse $ map delay . strengthen . assert_total (>>= nf) . relax . force
  Bind {biem} x f >>= nf with (order {rel=NoWeaker} biem em)
    _ | Left _  = Bind x $ \x => assert_total $ relax (f x) >>= nf
    _ | Right _ = Bind {biem} x $ \x => assert_total $ relax (f x) >>= relax . nf
  Labelled l x >>= nf = label l $ x >>= nf

-----------------------------------------
--- Detour: special list of lazy gens ---
-----------------------------------------

namespace GenAlternatives

  export %inline
  Nil : GenAlternatives False em a
  Nil = MkGenAlts []

  export %inline
  (::) : {em : _} ->
         lem `NoWeaker` em =>
         rem `NoWeaker` em =>
         (0 _ : IfUnsolved e True) =>
         (0 _ : IfUnsolved em NonEmpty) =>
         (0 _ : IfUnsolved lem em) =>
         (0 _ : IfUnsolved rem em) =>
         Lazy (Gen lem a) -> Lazy (GenAlternatives e rem a) -> GenAlternatives ne em a
  x :: xs = MkGenAlts $ (1, relax x) :: mapTaggedLazy relax xs.unGenAlts

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
  xs ++ ys = MkGenAlts $ mapTaggedLazy relax xs.unGenAlts ++ mapTaggedLazy relax ys.unGenAlts

  public export %inline
  length : GenAlternatives ne em a -> Nat
  length $ MkGenAlts alts = length alts

  export %inline
  processAlternatives : (Gen em a -> Gen em b) -> GenAlternatives ne em a -> GenAlternatives ne em b
  processAlternatives = flip mapOneOf

  export %inline
  processAlternativesMaybe : (Gen em a -> Maybe $ Lazy (Gen em b)) -> GenAlternatives ne em a -> GenAlternatives False em b
  processAlternativesMaybe f $ MkGenAlts xs = MkGenAlts $ mapMaybe (\(t, x) => (t,) <$> f x) xs

  export %inline
  processAlternatives'' : (Gen em a -> GenAlternatives neb em b) -> GenAlternatives nea em a -> GenAlternatives (nea && neb) em b
  processAlternatives'' f = mapGens where

    mapWeight : forall a, nea. (Nat1 -> Nat1) -> GenAlternatives nea em a -> GenAlternatives nea em a
    mapWeight f $ MkGenAlts xs = MkGenAlts $ xs <&> mapFst f

    mapGens : GenAlternatives nea em a -> GenAlternatives (nea && neb) em b
    mapGens $ MkGenAlts xs = MkGenAlts $ xs `bind` \(w, x) => unGenAlts $ mapWeight (w *) $ f x

  export %inline
  processAlternatives' : (Gen em a -> GenAlternatives ne em b) -> GenAlternatives ne em a -> GenAlternatives ne em b
  processAlternatives' f xs = rewrite sym $ andSameNeutral ne in processAlternatives'' f xs

  export %inline
  relax : GenAlternatives True em a -> GenAlternatives ne em a
  relax $ MkGenAlts alts = MkGenAlts $ relaxT alts

  export %inline
  strengthen : GenAlternatives ne em a -> Maybe $ GenAlternatives True em a
  strengthen $ MkGenAlts xs = MkGenAlts <$> strengthen xs

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
    xs <|> ys = MkGenAlts $ xs.unGenAlts <|> ys.unGenAlts

  -- implementation for `Monad` is below --

export
{em : _} -> Cast (LazyLst ne a) (GenAlternatives ne em a) where
  cast = MkGenAlts . map (\x => (1, pure x))

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
    DT : AltsNonEmpty True   MaybeEmptyDeep
    Sx : AltsNonEmpty altsNe MaybeEmpty

  export %defaulthint
  altsNonEmptyTrue : {em : _} -> AltsNonEmpty True em
  altsNonEmptyTrue {em=NonEmpty      } = NT
  altsNonEmptyTrue {em=MaybeEmptyDeep} = DT
  altsNonEmptyTrue {em=MaybeEmpty    } = Sx

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export
oneOf : {em : _} ->
        alem `NoWeaker` em =>
        AltsNonEmpty altsNe em =>
        (0 _ : IfUnsolved alem em) =>
        (0 _ : IfUnsolved altsNe $ em /= MaybeEmpty) =>
        GenAlternatives altsNe alem a -> Gen em a
oneOf {em=NonEmpty} @{NN} @{NT} $ MkGenAlts xs = mkOneOf xs
oneOf {em=MaybeEmptyDeep} @{_} @{DT} x = case x of MkGenAlts xs => mkOneOf xs
oneOf {em=MaybeEmpty} x = case x of MkGenAlts xs => do
  maybe Empty mkOneOf $ strengthen $ flip mapMaybe xs $
    \wg => (fst wg,) . delay <$> Gen.strengthen {em=MaybeEmptyDeep} (snd wg)

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : {em : _} ->
            alem `NoWeaker` em =>
            AltsNonEmpty altsNe em =>
            (0 _ : IfUnsolved alem em) =>
            (0 _ : IfUnsolved altsNe $ em /= MaybeEmpty) =>
            LazyLst altsNe (Nat1, Lazy (Gen alem a)) -> Gen em a
frequency = oneOf . MkGenAlts

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : {em : _} ->
           AltsNonEmpty altsNe em =>
           (0 _ : IfUnsolved em NonEmpty) =>
           (0 _ : IfUnsolved altsNe $ em /= MaybeEmpty) =>
           LazyLst altsNe a -> Gen em a
elements = oneOf {alem=NonEmpty} . altsFromList

export %inline
elements' : Foldable f =>
            (0 _ : IfUnsolved f List) =>
            f a -> Gen0 a
elements' xs = elements $ relaxF $ fromList $ toList xs

------------------------------
--- Analysis of generators ---
------------------------------

||| Shallow alternatives of a generator.
|||
||| If the given generator is made by one of `oneOf`, `frequency` or `elements`,
||| this function returns alternatives which this generators contains.
||| Otherwise it retuns a single-element alternative list containing given generator.
|||
||| In a sense, this function is a reverse function of `oneOf`, i.g.
||| `oneOf $ alternativesOf g` must be equivalent to `g` and
||| `alternativesof $ oneOf gs` must be equivalent to `gs`.
export
alternativesOf : {em : _} -> Gen em a -> GenAlternatives True em a
alternativesOf $ OneOf oo     = MkGenAlts $ unGenAlts $ mapOneOf oo relax
alternativesOf $ Labelled l x = processAlternatives (label l) $ alternativesOf x
alternativesOf g              = [g]

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

||| Returns generator with internal structure hidden for `alternativesOf`,
||| except for an empty generator, which would still be returned as an empty generator.
|||
||| This function must not change distribution when the resulting generator used with usual `Gen` combinators.
|||
||| Please notice that this function does NOT influence to the result of `deepAlternativesOf`, if depth is increased by 1.
export
forgetAlternatives : {em : _} -> Gen em a -> Gen em a
forgetAlternatives g@(OneOf {}) = case canBeNotImmediatelyEmpty em of
  Right _   => single g
  Left Refl => maybe Empty single $ strengthen {em=MaybeEmptyDeep} g
  where
    %inline single : iem `NoWeaker` MaybeEmptyDeep => iem `NoWeaker` em => Gen iem a -> Gen em a
    single g = label "forgetAlternatives" $ OneOf $ MkGenAlts [(1, g)]
    -- `mkOneOf` is not used here intentionally, since if `mkOneOf` can be changed to eliminate single-element `MkGenAlts`'s,
    -- we still want such behaviour here.
forgetAlternatives (Labelled l x) = label l $ forgetAlternatives x
forgetAlternatives g = g

||| Returns generator with internal structure hidden to anything, including combinators,
||| except for an empty generator, which would still be returned as an empty generator.
|||
||| Apply with care! Don't use until you understand what you are doing!
||| Most probably, you need the lighter version of this function called `forgetAlternatives`.
||| The difference is that `forgetAlternatives` do not influence on the resulting distribution,
||| when this function may ruin it unexpectedly.
|||
||| But despite `forgetAlternatives`, this function acts on `deepAlternativesOf`
||| like `forgetAlternatives` acts on `alternativesOf`,
||| i.e. `deepAlternativesOf` would give a single alternative for any depth
||| being applied to the result of this function.
export
forgetStructure : {em : _} -> Gen em a -> Gen em a
forgetStructure Empty     = Empty
forgetStructure g@(Raw _) = g
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
export
infix 8 `mapAlternativesOf`
      , `mapAlternativesWith`

export
{em : _} -> Monad (GenAlternatives True em) where
  xs >>= f = flip processAlternatives' xs $ alternativesOf . (>>= oneOf . f)

----------------------------------------
--- Additional composition functions ---
----------------------------------------

||| Associative composition of two generators, merging shallow alternatives of given two generators
|||
||| This operation being applied to arguments `a` and `b` is *not* the same as `oneOf [a, b]`.
||| Generator ``a `withAlts` b`` has equal probabilities of all shallow alternatives of generators `a` and `b`.
||| For example, when there are generators
||| ```idris
||| g1 = oneOf [elems [0, 1, 2, 3], elems [4, 5]]
||| g2 = oneOf elemts [10, 11, 12, 13, 14, 15]
||| ```
||| generator ``g1 `withAlts` g2`` would be equivalent to
||| `oneOf [elems [0, 1, 2, 3], elems [4, 5], pure 10, pure 11, pure 12, pure 13, pure 14, pure 15]`.
|||
||| In other words, ``a `withAlts` b`` must be equivalent to `oneOf $ alternativesOf a ++ alternativesOf b`.
export %inline
withAlts : {em : _} -> Gen em a -> Gen em a -> Gen em a
a `withAlts` b = oneOf $ alternativesOf a ++ alternativesOf b

-- As of `<|>`
export
infixr 2 `withAlts`

||| Associative composition of two generators, merging deep alternatives of given two generators
|||
||| This operation being applied to arguments `a` and `b` is *not* the same as `oneOf [a, b]`.
||| Generator ``a `withDeepAlts` b`` has equal probabilities of all deep alternatives of generators `a` and `b`.
||| For example, when there are generators
||| ```idris
||| g1 = oneOf [elems [0, 1, 2, 3], elems [4, 5]]
||| g2 = oneOf elemts [10, 11, 12, 13, 14, 15]
||| ```
||| generator ``withDeepAlts n g1 g2`` with `n >= 2` would be equivalent to
||| `oneOf elements [0, 1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15]`.
|||
||| In other words, ``withDeepAlts d a b`` must be equivalent to `oneOf $ deepAlternativesOf d a ++ deepAlternativesOf d b`.
export %inline
withDeepAlts : {em : _} -> (depth : Nat) -> Gen em a -> Gen em a -> Gen em a
withDeepAlts depth a b = oneOf $ deepAlternativesOf depth a ++ deepAlternativesOf depth b

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

export infixl 4 `suchThat`

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

||| More elegant version of `suchThat_withPrf` for fuelled generators.
|||
||| Tries to repeat generation until there is some fuel, and fallback to `suchThat_withPrf` in case there isn't.
export
retryUntil_withPrf : (p : a -> Bool) -> (Fuel -> Gen em a) -> Fuel -> Gen0 $ a `Subset` So . p
retryUntil_withPrf p f Dry           = f Dry `suchThat_withPrf` p
retryUntil_withPrf p f fl'@(More fl) = do
  x <- relax $ f fl'
  case @@ p x of
    (True ** prf) => pure $ Element x $ eqToSo prf
    (False ** _)  => retryUntil_withPrf p f fl

||| More elegant version of `suchThat` for fuelled generators.
|||
||| Tries to repeat generation until there is some fuel, and fallback to `suchThat` in case there isn't.
public export %inline
retryUntil : (p : a -> Bool) -> (Fuel -> Gen em a) -> Fuel -> Gen0 a
retryUntil p f = map fst . retryUntil_withPrf p f

||| More elegant version of `suchThat_dec` for fuelled generators.
|||
||| Tries to repeat generation until there is some fuel, and fallback to `suchThat_dec` in case there isn't.
export
retryUntil_dec : (p : (x : a) -> Dec (prop x)) -> (Fuel -> Gen em a) -> Fuel -> Gen0 $ Subset a prop
retryUntil_dec p f Dry           = f Dry `suchThat_dec` p
retryUntil_dec p f fl'@(More fl) = do
  x <- relax $ f fl'
  case p x of
    Yes p => pure $ Element x p
    No _  => retryUntil_dec p f fl

-------------------------------
--- Variation in generation ---
-------------------------------

iterate : forall a. Nat -> (a -> a) -> a -> a
iterate Z     _ x = x
iterate (S n) f x = iterate n f $ f x

-- TODO to reimplement `variant` to ensure that preserves the structure as far as it can.
export
variant : {em : _} -> Nat -> Gen em a -> Gen em a
variant _ Empty = Empty
variant Z gen   = gen
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
