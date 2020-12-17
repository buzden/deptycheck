module Test.DepTyCheck.Gen

import Data.DPair
import Data.List
import Data.List.Lazier
import Data.Stream
import Data.Vect

import Decidable.Equality

import Syntax.WithProof

import public System.Random.Simple

%default total

---------------------------------------------
--- General decisions and magic constants ---
---------------------------------------------

-- All of those can (and even should) be generalized some day.

public export %inline
Seed : Type
Seed = StdGen

-- TODO to make this externally tunable somehow.
RawFilteringAttempts : Nat
RawFilteringAttempts = 100

-------------------------------------------------
--- General utility functions and definitions ---
-------------------------------------------------

splitSeed : Seed -> (Seed, Seed)
splitSeed = bimap (snd . next) (snd . next) . split

public export
HavingTrue : (a : Type) -> (a -> Bool) -> Type
HavingTrue a p = Subset a \x => p x = True

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

export
data Gen : Type -> Type where
  Uniform : LzList a -> Gen a
  UniGens : LzList (Gen a) -> Gen a
  Raw     : (Seed -> Maybe a) -> Gen a

-- TODO To think about arbitrary discrete final probability distribution instead of only uniform.

export
bound : Gen a -> Maybe Nat
bound (Uniform xs) = Just $ length xs
bound (UniGens gs) = sum <$> traverse (assert_total bound) gs
bound (Raw _)      = Nothing

export
chooseAny : Random a => Gen a
chooseAny = Raw $ Just . fst . random

export
choose : Random a => (a, a) -> Gen a
choose bounds = Raw $ Just . fst . randomR bounds

pickAny : LzList a -> Seed -> Maybe a
pickAny xs s = case @@ xs.length of
  (Z   ** _)   => Nothing
  (S _ ** prf) => Just $ index xs rewrite prf in fst $ random s

export
unGen : Gen a -> Seed -> Maybe a
unGen (Uniform xs) = pickAny xs
unGen (Raw sf)     = sf
unGen (UniGens gs) = \s => let (s1, s2) = splitSeed s in
                           pickAny gs s1 >>= flip (assert_total unGen) s2

export %inline
unGenWithFallback : Gen a -> Gen a -> Seed -> Maybe a
unGenWithFallback main fallback s =
  case unGen main s of
    r@(Just _) => r
    Nothing => unGen fallback s

export
Functor Gen where
  map f (Uniform xs) = Uniform $ map f xs
  map f (UniGens gs) = UniGens $ assert_total $ map f <$> gs
  map f (Raw gena)   = Raw $ map f . gena

apAsRaw : Gen (a -> b) -> Gen a -> Gen b
apAsRaw generalF generalA = Raw \s => let (s1, s2) = splitSeed s in
  unGen generalF s1 <*> unGen generalA s2

export
Applicative Gen where
  pure x = Uniform [x]

  Uniform fs <*> Uniform xs = Uniform $ fs <*> xs
  Uniform fs <*> UniGens gs = UniGens $ [| map fs gs |]
  UniGens gs <*> Uniform xs = UniGens $ [| (\gab, a => map (flip apply a) gab) gs xs |]
  UniGens fs <*> UniGens gs = UniGens $ assert_total $ [| fs <*> gs |]

  rawF@(Raw {}) <*> generalA = apAsRaw rawF generalA
  generalF <*> rawA@(Raw {}) = apAsRaw generalF rawA

export
Alternative Gen where
  empty = Uniform []
  UniGens ls <|> UniGens rs = UniGens $ ls ++ rs
  UniGens ls <|> generalR   = UniGens $ ls ++ [generalR]
  generalL   <|> UniGens rs = UniGens $ [generalL] ++ rs
  generalL   <|> generalR   = UniGens $ [generalL, generalR]

export
oneOf : List (Gen a) -> Gen a
oneOf = choice

export
Monad Gen where
  g >>= c = Raw \s =>
    let (s1, s2) = splitSeed s in
    unGen g s1 >>= \a => unGen (c a) s2

export
mapMaybe : (a -> Maybe b) -> Gen a -> Gen b
mapMaybe p (Uniform l) = Uniform $ mapMaybe p l
mapMaybe p (UniGens l) = UniGens $ assert_total $ mapMaybe p <$> l
mapMaybe p (Raw sf)    = Raw \r =>
  choice $ map (\r => sf r >>= p) $ take RawFilteringAttempts $ countFrom r $ snd . next

export
suchThat_withPrf : Gen a -> (p : a -> Bool) -> Gen $ a `HavingTrue` p
suchThat_withPrf g p = mapMaybe lp g where
  lp : a -> Maybe $ a `HavingTrue` p
  lp x = case @@ p x of
    (True ** prf) => Just $ Element x prf
    (False ** _)  => Nothing

infixl 4 `suchThat`

public export
suchThat : Gen a -> (a -> Bool) -> Gen a
suchThat g p = fst <$> suchThat_withPrf g p

||| Filters the given generator so, that resulting values `x` are solutions of equation `y = f x` for given `f` and `y`.
export
suchThat_invertedEq : DecEq b => Gen a -> (y : b) -> (f : a -> b) -> Gen $ Subset a \x => y = f x
suchThat_invertedEq g y f = mapMaybe pep g where
  pep : a -> Maybe $ Subset a \x => y = f x
  pep x = case decEq y $ f x of
    Yes prf => Just $ Element x prf
    No _    => Nothing

-- TODO to reimplement `variant` to ensure that variant of `Uniform` is left `Uniform`.
export
variant : Nat -> Gen a -> Gen a
variant Z       gen = gen
variant x@(S _) gen = Raw $ unGen gen . index x . iterate (snd . split)

export
uniform : LzList a -> Gen a
uniform = Uniform

export
listOf : Gen a -> {default (choose (0, 10)) length : Gen Nat} -> Gen (List a)
listOf g = sequence $ replicate !length g

export
vectOf : Gen a -> {n : Nat} -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
