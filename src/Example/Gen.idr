module Example.Gen

import Control.Monad.Identity
import Control.Monad.Reader

import Data.List
import Data.Vect

import Example.Random

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

public export %inline
Seed : Type
Seed = StdGen

-- No "size" parameter in this definition unlike the quickcheck's `Gen`!
export
Gen : Type -> Type
Gen = Reader Seed

public export %inline
MkGen : (Seed -> a) -> Gen a
MkGen g = MkReaderT $ Id . g

public export %inline
unGen : Gen a -> Seed -> a
unGen = flip runReader

---------------------------------
--- Particular general `Gen`s ---
---------------------------------

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
oneof : {n : Nat} -> Vect (S n) (Gen a) -> Gen a
oneof v = index !chooseAny v

export
pairOf : Gen a -> Gen b -> Gen (a, b)
pairOf l r = (,) <$> l <*> r

export
listOf : Gen a -> Gen (List a)
listOf g = sequence $ replicate !chooseAny g

export
vectOf : Gen a -> {n : Nat} -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
