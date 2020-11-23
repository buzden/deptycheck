module Example.Gen

import Data.List
import public Data.Vect

import public Example.Random

%default total

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

public export %inline
Seed : Type
Seed = StdGen

-- No "size" parameter in this definition unlike the quickcheck's `Gen`!
public export
record Gen a where
  constructor MkGen
  unGen : Seed -> a

export
Functor Gen where
  map f (MkGen gena) = MkGen $ f . gena

export
Applicative Gen where
  pure x = MkGen $ const x
  (MkGen f) <*> (MkGen x) = MkGen $ \r =>
    let (r1, r2) = bimap (snd . next) (snd . next) $ split r in
    f r1 $ x r2

export
Monad Gen where
  (MkGen l) >>= f = MkGen $ \r =>
    let (r1, r2) = bimap (snd . next) (snd . next) $ split r in
    unGen (f $ l r1) r2

---------------------------------
--- Particular general `Gen`s ---
---------------------------------

export
covering
suchThat : Gen a -> (a -> Bool) -> Gen a
suchThat (MkGen f) p = MkGen \r => findOrDie r where
  findOrDie : Seed -> a
  findOrDie r = let v = f r in
                if p v then v else findOrDie $ snd $ next r

export
chooseAny : Random a => Gen a
chooseAny = MkGen $ fst . random

export
choose : Random a => (a, a) -> Gen a
choose bounds = MkGen $ fst . randomR bounds

export
variant : Nat -> Gen a -> Gen a
variant v gen = MkGen (\r => unGen gen $ getV (S v) r)
  where
    getV : Nat -> Seed -> Seed
    getV Z     r = r
    getV (S n) r = getV n $ snd $ split r

export
promote : (a -> Gen b) -> Gen (a -> b)
promote f = MkGen (\r, x => unGen (f x) r)

export
oneOf : {n : Nat} -> Vect (S n) (Gen a) -> Gen a
oneOf v = index !chooseAny v

export
pairOf : Gen a -> Gen b -> Gen (a, b)
pairOf l r = (,) <$> l <*> r

export
listOf : Gen a -> Gen (List a)
listOf g = sequence $ replicate !chooseAny g

export
vectOf : Gen a -> {n : Nat} -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
