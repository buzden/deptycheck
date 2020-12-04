module Test.DepTyCheck.Gen

import Data.DPair
import Data.List
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

index' : (l : List a) -> Fin (length l) -> a
index' (x::_)  FZ     = x
index' (x::xs) (FS i) = index' xs i

public export
HavingTrue : (a : Type) -> (a -> Bool) -> Type
HavingTrue a p = Subset a \x => p x = True

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

public export
data Gen : Type -> Type where
  Uniform : List a -> Gen a            -- TODO to think about arbitrary discrete final probability distribution instead of only uniform
  Raw     : (Seed -> Maybe a) -> Gen a -- No "size" parameter in the `Seed -> ...` function unlike the quickcheck's `Gen`!

export
bound : Gen a -> Maybe Nat
bound (Uniform xs) = Just $ length xs
bound (Raw _)      = Nothing

export
chooseAny : Random a => Gen a
chooseAny = Raw $ Just . fst . random

export
choose : Random a => (a, a) -> Gen a
choose bounds = Raw $ Just . fst . randomR bounds

export
unGen : Gen a -> Seed -> Maybe a
unGen (Uniform [])        _ = Nothing
unGen (Uniform xs@(_::_)) s = Just $ index' xs $ fst $ random s
unGen (Raw sf)            s = sf s

export
Functor Gen where
  map f (Uniform xs) = Uniform $ map f xs
  map f (Raw gena)   = Raw $ map f . gena

export
Applicative Gen where
  pure x = Uniform [x]
  Uniform fs <*> Uniform xs = Uniform $ fs <*> xs
  generalF   <*> generalA   = Raw \s => let (s1, s2) = splitSeed s in
    unGen generalF s1 <*> unGen generalA s2

export
Alternative Gen where
  empty = Uniform []
  Uniform ls <|> Uniform rs = Uniform $ ls ++ rs
  generalL   <|> generalR   = Raw \s =>
    let (sb, l, r) = bimap (unGen generalL) (unGen generalR) . splitSeed <$> splitSeed s in
    case (l, r) of
      (Just vl, Just vr) => Just $ if fst $ random sb then vl else vr
      _ => l <|> r -- take the only `Just`, if there is some.

export
oneOf : List (Gen a) -> Gen a
oneOf ls = choice $ reorderUniforms ls where
  -- Places `Uniform`s at those position where `foldr` (as an implementation detail of `choice`)
  -- would first pick them preserving uniform as long as possible.
  reorderUniforms : List (Gen a) -> List (Gen a)
  reorderUniforms xs = let (nonUni, uni) = partition isNonUni xs in nonUni ++ uni where
    isNonUni : Gen a -> Bool
    isNonUni (Uniform _) = True
    isNonUni _           = False

export
Monad Gen where
  Uniform ls >>= c = oneOf $ c <$> ls
  (Raw sf)   >>= c = Raw \s =>
    let (s1, s2) = splitSeed s in
    sf s1 >>= \a => unGen (c a) s2

export
mapMaybe : (a -> Maybe b) -> Gen a -> Gen b
mapMaybe p (Uniform l) = Uniform $ mapMaybe p l
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
uniform : List a -> Gen a
uniform = Uniform

export
listOf : Gen a -> {default (choose (0, 10)) length : Gen Nat} -> Gen (List a)
listOf g = sequence $ replicate !length g

export
vectOf : Gen a -> {n : Nat} -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
