module Test.DepTyCheck.Gen

import Data.DPair
import Data.List
import public Data.Vect

import Syntax.WithProof

import public System.Random.Simple

%default total

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

public export %inline
Seed : Type
Seed = StdGen

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

index' : (l : List a) -> Fin (length l) -> a
index' (x::_)  FZ     = x
index' (x::xs) (FS i) = index' xs i

export
unGen : Gen a -> Seed -> Maybe a
unGen (Uniform [])        _ = Nothing
unGen (Uniform xs@(_::_)) s = Just $ index' xs $ fst $ random s
unGen (Raw sf)            s = sf s

export
Functor Gen where
  map f (Uniform xs) = Uniform $ map f xs
  map f (Raw gena)   = Raw $ map f . gena

splitSeed : Seed -> (Seed, Seed)
splitSeed = bimap (snd . next) (snd . next) . split

export
Applicative Gen where
  pure x = Uniform [x]
  Uniform fs <*> Uniform xs = Uniform [f x | x <- xs, f <- fs]
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

-- Places `Uniform`s at those position where `foldr` (as an implementation detail of `choice`)
-- would first pick them preserving uniform as long as possible.
reorderUniforms : List (Gen a) -> List (Gen a)
reorderUniforms xs = let (nonUni, uni) = partition isNonUni xs in nonUni ++ uni where
  isNonUni : Gen a -> Bool
  isNonUni (Uniform _) = True
  isNonUni _           = False

export
oneOf : List (Gen a) -> Gen a
oneOf ls = choice $ reorderUniforms ls

export
Monad Gen where
  Uniform ls >>= c = oneOf $ c <$> ls
  (Raw sf)   >>= c = Raw \s =>
    let (s1, s2) = splitSeed s in
    sf s1 >>= \a => unGen (c a) s2

public export
HavingTrue : (a : Type) -> (a -> Bool) -> Type
HavingTrue a p = Subset a \x => p x = True

filter' : (p : a -> Bool) -> List a -> List $ a `HavingTrue` p
filter' p [] = []
filter' p (x::xs) = case @@ p x of
  (True ** prf) => Element x prf :: filter' p xs
  (False ** _)  => filter' p xs

export
filter_lawful : Gen a -> (p : a -> Bool) -> Gen $ a `HavingTrue` p
filter_lawful (Uniform f) p = Uniform $ filter' p f
filter_lawful (Raw f)     p = Raw \r => findOrFail RawFilteringAttempts r where
  findOrFail : Nat -> Seed -> Maybe $ a `HavingTrue` p
  findOrFail Z     _ = Nothing
  findOrFail (S n) r = case f r of
                         Just x => case @@ p x of
                           (True ** prf) => Just $ Element x prf
                           (False ** _)  => continue
                         Nothing => continue
                       where
                         continue : Maybe $ a `HavingTrue` p
                         continue = findOrFail n $ snd $ next r
  -- TODO to make this externally tunable somehow.
  RawFilteringAttempts : Nat
  RawFilteringAttempts = 100

public export
suchThat : Gen a -> (a -> Bool) -> Gen a
suchThat g p = fst <$> filter_lawful g p

-- TODO to reimplement `variant` to ensure that variant of `Uniform` is left `Uniform`.
export
variant : Nat -> Gen a -> Gen a
variant Z       gen = gen
variant x@(S _) gen = Raw \r => unGen gen $ getV x r
  where
    getV : Nat -> Seed -> Seed
    getV Z     r = r
    getV (S n) r = getV n $ snd $ split r

export
uniform : List a -> Gen a
uniform = Uniform

export
listOf : Gen a -> {default (choose (0, 10)) length : Gen Nat} -> Gen (List a)
listOf g = sequence $ replicate !length g

export
vectOf : Gen a -> {n : Nat} -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
