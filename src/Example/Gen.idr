module Example.Gen

import Control.Monad.Identity
import Control.Monad.Reader

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

chooseAny : Random a => Gen a
chooseAny = MkGen $ fst . random

choose : Random a => (a, a) -> Gen a
choose bounds = MkGen $ fst . randomR bounds

variant : Nat -> Gen a -> Gen a
variant v gen = MkGen (\r => unGen gen $ getV (S v) r)
  where
    getV : Nat -> Seed -> Seed
    getV Z     r = r
    getV (S n) r = getV n $ snd $ split r

promote : (a -> Gen b) -> Gen (a -> b)
promote f = MkGen (\r, x => unGen (f x) r)
