-- This is based on the David Christianen's port of QuickCheck to Idris 1

module System.Random.Pure

import Control.Monad.State

import Data.Fin

%default total

--------------------------------
--- Interface for seed types ---
--------------------------------

public export %inline
BaseGenTy : Type
BaseGenTy = Int64

public export
interface RandomGen g where
  next : g -> (g, BaseGenTy)
  genRange : g -> (BaseGenTy, BaseGenTy)
  split : g -> (g, g)

--------------------------------------------------------
--- Types for which values can be randomly generated ---
--------------------------------------------------------

public export
interface Random a where
  randomR : RandomGen g => (a, a) -> g -> (g, a)
  random : RandomGen g => g -> (g, a)

export
randomR' : Random a => RandomGen g => MonadState g m => (a, a) -> m a
randomR' bounds = let (g, x) = randomR bounds !get in put g $> x

export
random' : Random a => RandomGen g => MonadState g m => m a
random' = let (g, x) = random !get in put g $> x

export
[RandomThru] Random thru => Cast a thru => Cast thru a => Random a where
  randomR (lo, hi) = map cast . randomR {a=thru} (cast lo, cast hi)
  random = map cast . random {a=thru}

export %inline
randomThru : (0 thru : _) -> Random thru => Cast a thru => Cast thru a => Random a
randomThru thru = RandomThru {thru}

--- Nativest implementation ---

export
Random BaseGenTy where
  random gen = next gen
  randomR (lo, hi) gen = if lo > hi
                           then assert_total $ randomR (hi, lo) gen
                           else flip mapSnd (f n 1 gen) $ \v => lo + v `mod` k
    where
      k : BaseGenTy
      k = hi - lo + 1

      -- ERROR: b here (2^31-87) represents a baked-in assumption about genRange:
      b : BaseGenTy
      b = 2147483561

      iLogBase : BaseGenTy -> Nat
      iLogBase i = if i < b then 1 else S $ iLogBase $ assert_smaller i $ i `div` b where

      n : Nat
      n = iLogBase k

      -- Here we loop until we've generated enough randomness to cover the range:
      f : Nat -> BaseGenTy -> g -> (g, BaseGenTy)
      f Z      acc g = (g, acc)
      f (S n') acc g =
        let (g', x) = next g in
        -- We shift over the random bits generated thusfar (* b) and add in the new ones.
        f n' (x + acc * b) g'

public export %inline
randomThruNative : Cast a BaseGenTy => Cast BaseGenTy a => Random a
randomThruNative = randomThru BaseGenTy

--- Random Int ---

export %hint
RandomInt : Random Int
RandomInt = randomThruNative

--- Random Nat ---

export %hint
RandomNat : Random Nat
RandomNat = randomThruNative

--- Random Unit ---

export
Random Unit where
  randomR ((), ()) gen = map (const ()) $ next gen
  random gen = map (const ()) $ next gen

--- Random Fin ---

export %hint
RandomFin : {n : Nat} -> Random (Fin (S n))
RandomFin = randomThruNative where
  Cast (Fin $ S n) BaseGenTy where
    cast = fromInteger . cast
  Cast BaseGenTy (Fin $ S n) where
    cast = restrict {n} . cast

--- Random Char ---

export %hint
RandomChar : Random Char
RandomChar = randomThruNative

--- Random Bool ---

export %hint
RandomBool : Random Bool
RandomBool = randomThruNative where
  Cast Bool BaseGenTy where
    cast True  = 1
    cast False = 0
  Cast BaseGenTy Bool where
    cast x = x `mod` 2 == 0
