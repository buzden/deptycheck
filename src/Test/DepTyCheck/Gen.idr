module Test.DepTyCheck.Gen

import Control.Monad.Maybe
import public Control.Monad.Error.Interface
import Control.Monad.Random
import public Control.Monad.Random.Interface

import Data.Bool
import public Data.CheckedEmpty.List.Lazy
import Data.CheckedEmpty.List.Lazy.Elem
import Data.CheckedEmpty.List.Lazy.Quantifiers
import Data.CheckedEmpty.List.Lazy.Properties
import Data.Fuel
import public Data.Nat1
import Data.List
import Data.List.Lazy
import Data.List.Lazy.Extra
import Data.Vect

import Decidable.Equality

import public Language.Implicits.IfUnsolved

import Syntax.WithProof

import public Test.DepTyCheck.Gen.Emptiness
import public Test.DepTyCheck.Gen.Labels

%default total

-------------------------
--- Utility functions ---
-------------------------

randomFin : MonadRandom m => (n : Nat1) -> m $ Fin n.asNat
randomFin $ FromNat (S _) = getRandom

public export %inline
wrapLazy : (a -> b) -> Lazy a -> Lazy b
wrapLazy f = delay . f . force

%inline
wrapMaybeTaggedLazy : (a -> Maybe b) -> (tag, Lazy a) -> Maybe (tag, Lazy b)
wrapMaybeTaggedLazy f = traverse $ map delay . f . force

0 unpackTaggedLazy : Functor f => f (tag, Lazy a) -> f a
unpackTaggedLazy = map $ force . snd

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

record RawGen a where
  constructor MkRawGen
  unRawGen : forall m. MonadRandom m => CanManageLabels m => m a

export
data Gen : Emptiness -> Type -> Type

0 IsNonEmpty : Gen em a -> Type

export
record GenAlternatives (0 mustBeNotEmpty : Bool) (0 em : Emptiness) (a : Type)

0 All : (Gen em a -> Type) -> GenAlternatives ne em a -> Type

data Gen : Emptiness -> Type -> Type where

  Empty : Gen MaybeEmpty a

  Pure  : a -> Gen em a

  Raw   : RawGen a -> Gen em a

  OneOf : (gs : GenAlternatives True alem a) ->
          (0 _ : All IsNonEmpty gs) =>
          (0 _ : alem `NoWeaker` em) =>
          Gen em a

  Bind  : (0 _ : biem `NoWeaker` em) =>
          RawGen c -> (c -> Gen biem a) -> Gen em a

  Labelled : Label -> (g : Gen em a) -> (0 _ : IsNonEmpty g) => Gen em a

isEmpty : Gen em a -> Bool
isEmpty Empty = True
isEmpty _     = False

%inline
isNonEmpty : Gen em a -> Bool
isNonEmpty = not . isEmpty

IsNonEmpty g = isEmpty g === False

record GenAlternatives (0 mustBeNotEmpty : Bool) (0 em : Emptiness) (a : Type) where
  constructor MkGenAlts
  unGenAlts : LazyLst mustBeNotEmpty (Nat1, Lazy (Gen em a))

0 listOfAlts : GenAlternatives ne em a -> LazyLst ne $ Gen em a
listOfAlts $ MkGenAlts gs = unpackTaggedLazy gs

All p = All p . listOfAlts

0 Elem : Gen em a -> GenAlternatives ne em a -> Type
Elem g = Elem g . listOfAlts

(.totalWeight) : GenAlternatives True em a -> Nat1
(.totalWeight) = foldl1 (+) . map fst . unGenAlts

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

%hint
0 isNonEmptyGen1 : {g : Gen1 a} -> IsNonEmpty g
isNonEmptyGen1 {g=Pure _}       = Refl
isNonEmptyGen1 {g=Raw _}        = Refl
isNonEmptyGen1 {g=OneOf _}      = Refl
isNonEmptyGen1 {g=Bind _ _}     = Refl
isNonEmptyGen1 {g=Labelled _ _} = Refl

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
label l g with (isEmpty g) proof 0 prf
  label _ Empty | True  = Empty
  label l g     | False = Labelled l g

total
0 labelNonEmpty : {g : Gen em a} -> IsNonEmpty g => IsNonEmpty $ label l g
labelNonEmpty {g=Pure _}       = Refl
labelNonEmpty {g=Raw _}        = Refl
labelNonEmpty {g=OneOf _}      = Refl
labelNonEmpty {g=Bind _ _}     = Refl
labelNonEmpty {g=Labelled _ _} = Refl

------------------------------------------------
--- Technical stuff for mapping alternatives ---
------------------------------------------------

mapTaggedLazy : Functor f => (a -> b) -> f (tag, Lazy a) -> f (tag, Lazy b)
mapTaggedLazy f = map $ \x => (fst x, wrapLazy f $ snd x)

mapOneOf : GenAlternatives ne iem a -> (Gen iem a -> Gen em b) -> GenAlternatives ne em b
mapOneOf $ MkGenAlts gs = MkGenAlts . flip mapTaggedLazy gs

0 allMapTaggedLazy : {0 f : a -> b} -> {xs : LazyLst ne (tag, Lazy a)} ->
                     ({x : a} -> (0 _ : Elem x $ unpackTaggedLazy xs) -> p $ f x) ->
                     All p $ unpackTaggedLazy $ mapTaggedLazy f xs
allMapTaggedLazy h = allMap $ allMapForall $ \e => h $ elemMap _ e

0 allMapOneOf : {0 f : Gen iem a -> Gen em b} ->
                {gs : GenAlternatives ne iem a} ->
                ({x : Gen iem a} -> (0 _ : Elem x gs) -> p $ f x) ->
                All p $ mapOneOf gs f
allMapOneOf {gs=MkGenAlts _} = allMapTaggedLazy

mapElem : (xs : LazyLst ne a) -> ((x : a) -> (0 _ : Elem x xs) -> b) -> LazyLst ne b
mapElem []        _ = []
mapElem (x :: xs) f = f x Here :: mapElem xs (\y, e => f y $ There e)

mapTaggedLazyElem : (xs : LazyLst ne (tag, Lazy a)) ->
                    ((x : a) -> (0 _ : Elem x $ unpackTaggedLazy xs) -> b) ->
                    LazyLst ne (tag, Lazy b)
mapTaggedLazyElem xs f = mapElem xs $ \x, e => (fst x, delay $ f (snd x) $ elemMap _ e)

mapOneOfElem : (gs : GenAlternatives ne iem a) ->
               ((g : Gen iem a) -> (0 _ : Elem g gs) -> Gen em b) ->
               GenAlternatives ne em b
mapOneOfElem $ MkGenAlts gs = MkGenAlts . mapTaggedLazyElem gs

0 allMapElem : {xs : LazyLst ne a} ->
               {0 f : (x : a) -> (0 _ : Elem x xs) -> b} ->
               ({x : a} -> (0 e : Elem x xs) -> p $ f x e) ->
               All p $ mapElem xs f
allMapElem {xs=[]}      _ = []
allMapElem {xs=x :: xs} h = h Here :: allMapElem (\e => h $ There e)

0 allMapTaggedLazyElem : {xs : LazyLst ne (tag, Lazy a)} ->
                         {0 f : (x : a) -> (0 _ : Elem x $ unpackTaggedLazy xs) -> b} ->
                         ({x : a} -> (0 e : Elem x $ unpackTaggedLazy xs) -> p $ f x e) ->
                         All p $ unpackTaggedLazy $ mapTaggedLazyElem xs f
allMapTaggedLazyElem h = allMap $ allMapElem $ \e => h $ elemMap _ e

0 allMapOneOfElem : {gs : GenAlternatives ne iem a} ->
                    {0 f : (g : Gen iem a) -> (0 _ : Elem g gs) -> Gen em b} ->
                    ({g : Gen iem a} -> (0 e : Elem g gs) -> p $ f g e) ->
                    All p $ mapOneOfElem gs f
allMapOneOfElem {gs=MkGenAlts _} = allMapTaggedLazyElem

-----------------------------
--- Emptiness tweakenings ---
-----------------------------

export
relax : (0 _ : iem `NoWeaker` em) => Gen iem a -> Gen em a
0 relaxNonEmpty : {g : Gen iem a} -> IsNonEmpty g => IsNonEmpty $ relax @{nw} g

relax @{nw} Empty           = rewrite maybeEmptyIsMinimal nw in Empty
relax $ Pure x              = Pure x
relax $ Raw x               = Raw x
relax $ OneOf @{ne} @{nw} x = OneOf @{ne} @{transitive' nw %search} x
relax $ Bind @{nw} x f      = Bind @{transitive' nw %search} x f
relax $ Labelled l x        = Labelled @{relaxNonEmpty} l $ relax x

relaxNonEmpty {g=Pure _}       = Refl
relaxNonEmpty {g=Raw _}        = Refl
relaxNonEmpty {g=OneOf _}      = Refl
relaxNonEmpty {g=Bind _ _}     = Refl
relaxNonEmpty {g=Labelled _ _} = Refl

--------------------
--- More utility ---
--------------------

nonEmpty : Gen em a -> Maybe $ Gen em a
nonEmpty Empty = Nothing
nonEmpty x     = Just x

0 nonEmptyNonEmpty : {g : Gen em a} -> IsJust (nonEmpty g) =>
                     IsNonEmpty $ fromJust $ nonEmpty g
nonEmptyNonEmpty {g=Pure _}       = Refl
nonEmptyNonEmpty {g=Raw _}        = Refl
nonEmptyNonEmpty {g=OneOf _}      = Refl
nonEmptyNonEmpty {g=Bind _ _}     = Refl
nonEmptyNonEmpty {g=Labelled _ _} = Refl

mapMaybeTaggedLazy : (a -> Maybe b) -> LazyLst ne (tag, Lazy a) -> LazyLst0 (tag, Lazy b)
mapMaybeTaggedLazy = mapMaybe . wrapMaybeTaggedLazy

0 allMapMaybeJustTaggedLazy : {f : a -> Maybe b} ->
                              {xs : LazyLst ne (tag, Lazy a)} ->
                              ((x : a) ->
                               (0 _ : IsJust $ f x) ->
                               p $ fromJust $ f x) ->
                              All p $ unpackTaggedLazy $ mapMaybeTaggedLazy f xs
allMapMaybeJustTaggedLazy h = allMap $ allMapMaybeJust helper
  where
    helper : (x : (tag, Lazy a)) ->
             {0 _ : IsJust $ wrapMaybeTaggedLazy f x} ->
             p $ force $ snd $ fromJust $ wrapMaybeTaggedLazy f x
    helper (w, x) with (f x) proof 0 prf
      helper (w, x) | Just y = do
        let yIsJust : IsJust (f x) = rewrite prf in ItIsJust
        let Refl : y === fromJust (f x) = rewrite prf in Refl
        h x yIsJust

namespace OneOf

  public export
  data AltsNonEmpty : Bool -> Emptiness -> Type where
    NT : AltsNonEmpty True   NonEmpty
    Sx : AltsNonEmpty altsNe MaybeEmpty

  export %defaulthint
  altsNonEmptyTrue : {em : _} -> AltsNonEmpty True em
  altsNonEmptyTrue {em=NonEmpty}   = NT
  altsNonEmptyTrue {em=MaybeEmpty} = Sx

mkOneOfMaybeEmpty : (xs : LazyLst altsNe (Nat1, Lazy (Gen alem a))) ->
                    (0 _ : All IsNonEmpty $ unpackTaggedLazy xs) =>
                    Gen0 a
mkOneOfMaybeEmpty []                  = Empty
mkOneOfMaybeEmpty (x :: xs) @{_ :: _} = OneOf $ MkGenAlts $ x :: xs

mkOneOf : {em : _} ->
          (0 _ : alem `NoWeaker` em) =>
          (0 _ : AltsNonEmpty altsNe em) =>
          LazyLst altsNe (Nat1, Lazy (Gen alem a)) ->
          Gen em a
mkOneOf {em=NonEmpty} @{nw} @{NT} xs with 0 (nonEmptyIsMaximal nw)
  _ | Refl = OneOf @{allTrue isNonEmptyGen1} $ MkGenAlts xs
mkOneOf {em=MaybeEmpty} xs =
  mkOneOfMaybeEmpty (mapMaybeTaggedLazy nonEmpty xs)
    @{allMapMaybeJustTaggedLazy {f=nonEmpty} $ \_, _ => nonEmptyNonEmpty}

--------------------------
--- Running generators ---
--------------------------

--- Non-empty generators ---

export
unGen1 : MonadRandom m => CanManageLabels m => Gen1 a -> m a
unGen1 $ Pure x         = pure x
unGen1 $ Raw sf         = sf.unRawGen
unGen1 $ OneOf @{_} @{nw} oo with 0 (nonEmptyIsMaximal nw)
  _ | Refl = assert_total unGen1 . force . pickWeighted oo.unGenAlts . finToNat =<< randomFin oo.totalWeight
unGen1 $ Bind @{nw} x f with 0 (nonEmptyIsMaximal nw)
  _ | Refl = x.unRawGen >>= unGen1 . f
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
pick gen = initSeed <&> flip evalRandom (unGen' gen)

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
Functor (Gen em)
0 mapNonEmpty : {g : Gen iem a} -> IsNonEmpty g => IsNonEmpty $ f <$> g

Functor (Gen em) where
  map f $ Empty          = Empty
  map f $ Pure x         = Pure $ f x
  map f $ Raw sf         = Raw $ f <$> sf
  map f $ OneOf @{ne} oo = OneOf @{allMapOneOf $ \e => mapNonEmpty @{indexAll e ne}} $ mapOneOf oo $ assert_total $ map f
  map f $ Bind x g       = Bind x $ map f . g
  map f $ Labelled l x   = Labelled @{mapNonEmpty} l $ map f x

mapNonEmpty {g=Pure _}       = Refl
mapNonEmpty {g=Raw _}        = Refl
mapNonEmpty {g=OneOf _}      = Refl
mapNonEmpty {g=Bind _ _}     = Refl
mapNonEmpty {g=Labelled _ _} = Refl

private infixl 3 <**>

(<**>) : (g : Gen lem $ a -> b) -> (h : Gen rem a) -> Gen (min lem rem) b
0 apNonEmpty : {g, h : _} -> IsNonEmpty g => IsNonEmpty h => IsNonEmpty $ g <**> h

g <**> h with (isEmpty g) proof 0 prfLeft | (isEmpty h) proof 0 prfRight
  Empty <**> _ | _ | _ = rewrite minMaybeEmptyLeft rem in Empty
  _ <**> Empty | _ | _ = rewrite minMaybeEmptyRight lem in Empty

  Pure f <**> g | _ | _ = f <$> relax @{rightNoWeakerMin} g
  g <**> Pure x | _ | _ = relax @{leftNoWeakerMin} g <&> \f => f x

  Raw sfl <**> Raw sfr | _ | _ = Raw $ sfl <*> sfr

  Labelled l x <**> y | _     | False = Labelled @{apNonEmpty} l $ x <**> y
  x <**> Labelled l y | False | _     = Labelled @{apNonEmpty} l $ x <**> y

  OneOf @{ne} @{nw} oo <**> g | _ | False =
      OneOf @{allMapOneOf $ \e => apNonEmpty @{indexAll e ne}}
            @{minNoWeakerLeft nw} $
        mapOneOf oo $ \x => assert_total $ x <**> g
  g <**> OneOf @{ne} @{nw} oo | False | _ =
    OneOf @{allMapOneOf $ \e => apNonEmpty @{%search} @{indexAll e ne}}
          @{minNoWeakerRight nw} $
      mapOneOf oo $ \x => assert_total $ g <**> x

  Bind @{nw} x f <**> Raw y | _ | _ =
    Bind @{minNoWeakerLeft nw}  x $ \c => f c <**> Raw y
  Raw y <**> Bind @{nw} x f | _ | _ =
    Bind @{minNoWeakerRight nw} x $ \c => Raw y <**> f c

  Bind @{lnw} x f <**> Bind @{rnw} y g | _ | _ =
    Bind @{minNoWeaker lnw rnw} [| (x, y) |] $ \(l, r) => f l <**> g r

apNonEmpty with (isEmpty g) proof 0 prfLeft | (isEmpty h) proof 0 prfRight
  apNonEmpty {g=Empty}        {h}              | True  | _     impossible
  apNonEmpty {g}              {h=Empty}        | _     | True  impossible

  apNonEmpty {g=Pure _}       {h=Pure _}       | _     | _     = Refl
  apNonEmpty {g=Pure _}       {h=Raw _}        | _     | _     = Refl
  apNonEmpty {g=Pure _}       {h=OneOf _}      | _     | _     = Refl
  apNonEmpty {g=Pure _}       {h=Bind _ _}     | _     | _     = Refl
  apNonEmpty {g=Pure _}       {h=Labelled _ _} | _     | _     = Refl

  apNonEmpty {g=Raw _}        {h=Pure _}       | _     | _     = Refl
  apNonEmpty {g=OneOf _}      {h=Pure _}       | _     | _     = Refl
  apNonEmpty {g=Bind _ _}     {h=Pure _}       | _     | _     = Refl
  apNonEmpty {g=Labelled _ _} {h=Pure _}       | _     | _     = Refl

  apNonEmpty {g=Raw _}        {h=Raw _}        | _     | _     = Refl

  apNonEmpty {g=Labelled _ _} {h=Raw _}        | _     | False = Refl
  apNonEmpty {g=Labelled _ _} {h=OneOf _}      | _     | False = Refl
  apNonEmpty {g=Labelled _ _} {h=Bind _ _}     | _     | False = Refl
  apNonEmpty {g=Labelled _ _} {h=Labelled _ _} | _     | False = Refl

  apNonEmpty {g=Raw _}        {h=Labelled _ _} | False | False = Refl
  apNonEmpty {g=OneOf _}      {h=Labelled _ _} | False | False = Refl
  apNonEmpty {g=Bind _ _}     {h=Labelled _ _} | False | False = Refl

  apNonEmpty {g=OneOf _}      {h=Raw _}        | False | False = Refl
  apNonEmpty {g=OneOf _}      {h=OneOf _}      | False | False = Refl
  apNonEmpty {g=OneOf _}      {h=Bind _ _}     | False | False = Refl

  apNonEmpty {g=Bind _ _}     {h=OneOf _}      | False | False = Refl
  apNonEmpty {g=Raw _}        {h=OneOf _}      | False | False = Refl

  apNonEmpty {g=Raw _}        {h=Bind _ _}     | _     | False = Refl
  apNonEmpty {g=Bind _ _}     {h=Raw _}        | _     | False = Refl

  apNonEmpty {g=Bind _ _}     {h=Bind _ _}     | _     | False = Refl

export
Applicative (Gen em) where
  pure = Pure
  g <*> h = rewrite sym $ minSame em in g <**> h

private infixl 1 >>==

(>>==) : {rem : _} -> Gen lem a -> (a -> Gen rem b) -> Gen (min lem rem) b
0 bindNonEmpty : {f : a -> Gen1 b} -> IsNonEmpty g => IsNonEmpty $ g >>== f

Empty          >>== _  = rewrite minMaybeEmptyLeft rem in Empty
Pure x         >>== nf = relax @{rightNoWeakerMin} $ nf x
Raw g          >>== nf = Bind @{rightNoWeakerMin} g nf
Bind @{nw} x f >>== nf = Bind @{minNoWeakerLeft nw} x $ (>>== nf) . f
Labelled l x   >>== nf = label l $ x >>== nf

(OneOf @{ne} @{nw} (MkGenAlts gs) >>== nf) {rem=NonEmpty} =
  OneOf @{allMapTaggedLazy {f=assert_total (>>== nf)} $ \e => bindNonEmpty @{indexAll e ne}}
        @{minNoWeakerLeft nw} $
        MkGenAlts $ flip mapTaggedLazy gs $ assert_total (>>== nf)

-- Inlining `mkOneOf` for manual fusion
(OneOf oo >>== nf) {rem=MaybeEmpty} = do
  rewrite minMaybeEmptyRight lem
  mkOneOfMaybeEmpty
    (mapMaybeTaggedLazy (nonEmpty . assert_total (>>== nf)) oo.unGenAlts)
    @{allMapMaybeJustTaggedLazy {f=nonEmpty . assert_total (>>== nf)} $ \_, _ => nonEmptyNonEmpty}

bindNonEmpty {g=Pure _}              = relaxNonEmpty @{isNonEmptyGen1}
bindNonEmpty {g=Raw _}               = Refl
bindNonEmpty {g=Bind _ _}            = Refl
bindNonEmpty {g=Labelled _ _}        = labelNonEmpty @{bindNonEmpty}
bindNonEmpty {g=OneOf $ MkGenAlts _} = Refl

export
{em : _} -> Monad (Gen em) where
  g >>= h = rewrite sym $ minSame em in g >>== h

-----------------------------------------
--- Detour: special list of lazy gens ---
-----------------------------------------

namespace GenAlternatives

  export %inline
  Nil : GenAlternatives False em a
  Nil = MkGenAlts []

  export %inline
  (::) : (0 _ : lem `NoWeaker` em) =>
         (0 _ : rem `NoWeaker` em) =>
         (0 _ : IfUnsolved e True) =>
         (0 _ : IfUnsolved em NonEmpty) =>
         (0 _ : IfUnsolved lem em) =>
         (0 _ : IfUnsolved rem em) =>
         Lazy (Gen lem a) -> Lazy (GenAlternatives e rem a) -> GenAlternatives ne em a
  x :: xs = MkGenAlts $ (1, relax x) :: mapTaggedLazy relax xs.unGenAlts

  -- This concatenation breaks relative proportions in frequences of given alternative lists
  public export %inline
  (++) : (0 _ : lem `NoWeaker` em) =>
         (0 _ : rem `NoWeaker` em) =>
         (0 _ : IfUnsolved lem em) =>
         (0 _ : IfUnsolved rem em) =>
         (0 _ : IfUnsolved nel False) =>
         (0 _ : IfUnsolved ner False) =>
         GenAlternatives nel lem a -> Lazy (GenAlternatives ner rem a) -> GenAlternatives (nel || ner) em a
  xs ++ ys = MkGenAlts $ mapTaggedLazy relax xs.unGenAlts ++ mapTaggedLazy relax ys.unGenAlts

  public export %inline
  length : GenAlternatives ne em a -> Nat
  length = length . unGenAlts

  export %inline
  processAlternatives : (Gen em a -> Gen em b) -> GenAlternatives ne em a -> GenAlternatives ne em b
  processAlternatives = flip mapOneOf

  export %inline
  processAlternativesMaybe : (Gen em a -> Maybe $ Lazy (Gen em b)) -> GenAlternatives ne em a -> GenAlternatives False em b
  processAlternativesMaybe f = MkGenAlts . mapMaybe (traverse $ f . force) . unGenAlts

  export %inline
  processAlternatives'' : (Gen em a -> GenAlternatives neb em b) -> GenAlternatives nea em a -> GenAlternatives (nea && neb) em b
  processAlternatives'' f = mapGens where

    mapWeight : forall a, nea. (Nat1 -> Nat1) -> GenAlternatives nea em a -> GenAlternatives nea em a
    mapWeight f = MkGenAlts . map (mapFst f) . unGenAlts

    mapGens : GenAlternatives nea em a -> GenAlternatives (nea && neb) em b
    mapGens xs = MkGenAlts $ xs.unGenAlts `bind` \(w, x) => unGenAlts $ mapWeight (w *) $ f x

  export %inline
  processAlternatives' : (Gen em a -> GenAlternatives ne em b) -> GenAlternatives ne em a -> GenAlternatives ne em b
  processAlternatives' f xs = rewrite sym $ andSameNeutral ne in processAlternatives'' f xs

  export %inline
  relax : GenAlternatives True em a -> GenAlternatives ne em a
  relax = MkGenAlts . relaxT . unGenAlts

  export %inline
  strengthen : GenAlternatives ne em a -> Maybe $ GenAlternatives True em a
  strengthen = map MkGenAlts . strengthen . unGenAlts

  export
  Functor (GenAlternatives ne em) where
    map = processAlternatives . map

  export
  Applicative (GenAlternatives ne em) where
    pure x = [ pure x ]
    xs <*> ys = flip processAlternatives' xs $ flip processAlternatives ys . (<*>)

  export
  Alternative (GenAlternatives False em) where
    empty = []
    xs <|> ys = MkGenAlts $ xs.unGenAlts <|> ys.unGenAlts

  -- implementation for `Monad` is below --

export
Cast (LazyLst ne a) (GenAlternatives ne em a) where
  cast = MkGenAlts . map (\x => (1, pure x))

public export %inline
altsFromList : LazyLst ne a -> GenAlternatives ne em a
altsFromList = cast

----------------------------------
--- Creation of new generators ---
----------------------------------

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export
oneOf : {em : _} ->
        (0 _ : alem `NoWeaker` em) =>
        (0 _ : AltsNonEmpty altsNe em) =>
        (0 _ : IfUnsolved alem em) =>
        (0 _ : IfUnsolved altsNe $ em /= MaybeEmpty) =>
        GenAlternatives altsNe alem a -> Gen em a
oneOf = mkOneOf . unGenAlts

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : {em : _} ->
            (0 _ : alem `NoWeaker` em) =>
            (0 _ : AltsNonEmpty altsNe em) =>
            (0 _ : IfUnsolved alem em) =>
            (0 _ : IfUnsolved altsNe $ em /= MaybeEmpty) =>
            LazyLst altsNe (Nat1, Lazy (Gen alem a)) -> Gen em a
frequency = oneOf . MkGenAlts

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : {em : _} ->
           (0 _ : AltsNonEmpty altsNe em) =>
           (0 _ : IfUnsolved em NonEmpty) =>
           (0 _ : IfUnsolved altsNe $ em /= MaybeEmpty) =>
           LazyLst altsNe a -> Gen em a
elements = oneOf {alem=NonEmpty} . altsFromList

export %inline
elements' : Foldable f => (0 _ : IfUnsolved f List) => f a -> Gen0 a
elements' xs = elements $ fromList $ toList xs

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
alternativesOf : Gen em a -> GenAlternatives True em a
0 alternativesOfNonEmpty : {g : Gen em a} -> IsNonEmpty g => All IsNonEmpty $ alternativesOf g

alternativesOf $ OneOf oo     = mapOneOf oo relax
alternativesOf $ Labelled l x = mapOneOfElem (alternativesOf x) $ \g, e => Labelled l g @{indexAll e alternativesOfNonEmpty}
alternativesOf g              = [g]

alternativesOfNonEmpty {g=Pure _}        = [Refl]
alternativesOfNonEmpty {g=Raw _}         = [Refl]
alternativesOfNonEmpty {g=OneOf @{ne} _} = allMapOneOf $ \e => relaxNonEmpty @{indexAll e ne}
alternativesOfNonEmpty {g=Bind _ _}      = [Refl]
alternativesOfNonEmpty {g=Labelled _ _}  = allMapOneOfElem $ \_ => Refl

||| Any depth alternatives fetching.
|||
||| Alternatives of depth `0` are meant to be a single-item alternatives list with the original generator,
||| alternatives of depth `1` are those returned by the `alternativesOf` function,
||| alternatives of depth `n+1` are alternatives of all alternatives of depth `n` being flattened into a single alternatives list.
export
deepAlternativesOf : (depth : Nat) -> Gen em a -> GenAlternatives True em a
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
forgetAlternatives : Gen em a -> Gen em a
0 forgetAlternativesNonEmpty : {g : Gen iem a} -> IsNonEmpty g => IsNonEmpty $ forgetAlternatives g

forgetAlternatives g@(OneOf {})   = Labelled "forgetAlternatives" $ OneOf @{[Refl]} $ MkGenAlts [(1, g)]
forgetAlternatives $ Labelled l x = Labelled @{forgetAlternativesNonEmpty} l $ forgetAlternatives x
forgetAlternatives g              = g

forgetAlternativesNonEmpty {g=Pure _}       = Refl
forgetAlternativesNonEmpty {g=Raw _}        = Refl
forgetAlternativesNonEmpty {g=OneOf _}      = Refl
forgetAlternativesNonEmpty {g=Bind _ _}     = Refl
forgetAlternativesNonEmpty {g=Labelled _ _} = Refl

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
forgetStructure Empty             = Empty
forgetStructure g@(Raw _)         = g
forgetStructure g {em=NonEmpty}   = Raw $ MkRawGen $ unGen1 g
forgetStructure g {em=MaybeEmpty} = MkRawGen (unGen' g) `Bind` maybe Empty Pure

public export
processAlternatives : (Gen em a -> Gen em b) -> Gen em a -> GenAlternatives True em b
processAlternatives f = processAlternatives f . alternativesOf

public export
mapAlternativesOf : (a -> b) -> Gen em a -> GenAlternatives True em b
mapAlternativesOf = processAlternatives . map

public export %inline
mapAlternativesWith : Gen em a -> (a -> b) -> GenAlternatives True em b
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
  lp x with (p x) proof 0 prf
    _ | True  = Just $ Element x $ eqToSo prf
    _ | False = Nothing

export infixl 4 `suchThat`

public export
suchThat : Gen em a -> (a -> Bool) -> Gen0 a
suchThat g p = fst <$> suchThat_withPrf g p

export
suchThat_dec : Gen em a -> ((x : a) -> Dec $ prop x) -> Gen0 $ Subset a prop
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
retryUntil p = map fst .: retryUntil_withPrf p

||| More elegant version of `suchThat_dec` for fuelled generators.
|||
||| Tries to repeat generation until there is some fuel, and fallback to `suchThat_dec` in case there isn't.
export
retryUntil_dec : (p : (x : a) -> Dec $ prop x) -> (Fuel -> Gen em a) -> Fuel -> Gen0 $ Subset a prop
retryUntil_dec p f Dry           = f Dry `suchThat_dec` p
retryUntil_dec p f fl'@(More fl) = do
  x <- relax $ f fl'
  case p x of
    Yes p => pure $ Element x p
    No _  => retryUntil_dec p f fl

-------------------------------
--- Variation in generation ---
-------------------------------

iterate : Nat -> (a -> a) -> a -> a
iterate Z     _ = id
iterate (S n) f = iterate n f . f

-- TODO to reimplement `variant` to ensure that preserves the structure as far as it can.
export
variant : {em : _} -> Nat -> Gen em a -> Gen em a
variant _ Empty               = Empty
variant Z gen                 = gen
variant n gen {em=NonEmpty}   = Raw $ MkRawGen $ iterate n independent $ unGen1 gen
variant n gen {em=MaybeEmpty} = MkRawGen (iterate n independent $ unGen' gen) `Bind` maybe Empty Pure

-----------------------------
--- Particular generators ---
-----------------------------

export
listOf : {em : _} -> {default (choose (0, 10)) length : Gen em Nat} -> Gen em a -> Gen em $ List a
listOf g = sequence $ List.replicate !length g

export
vectOf : {em : _} -> {n : Nat} -> Gen em a -> Gen em $ Vect n a
vectOf = sequence . replicate n
