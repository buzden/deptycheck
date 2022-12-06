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

--------------------------------
--- Example of the seed type ---
--------------------------------

export
data StdGen = MkStdGen BaseGenTy BaseGenTy

export
someStdGen : StdGen
someStdGen = MkStdGen 23462 254334222987

export
Show StdGen where
  show (MkStdGen i j) = "MkStdGen " ++ show i ++ " " ++ show j

-- Blatantly stolen from Haskell
export
RandomGen StdGen where
  next (MkStdGen s1 s2) =
    let k : BaseGenTy = s1 `div` 53668 in
    let s1' : BaseGenTy  = 40014 * (s1 - k * 53668) - k * 12211 in
    let s1'' : BaseGenTy = if s1' < 0 then s1' + 2147483563 else s1' in
    let k' : BaseGenTy = s2 `div` 52774 in
    let s2' : BaseGenTy = 40692 * (s2 - k' * 52774) - k' * 3791 in
    let s2'' : BaseGenTy = if s2' <= 0 then s2' + 2147483399 else s2' in
    let z : BaseGenTy = s1'' - s2'' in
    let z' : BaseGenTy = if z < 1 then z + 2147483562 else z in
    (MkStdGen s1'' s2'', z')

  genRange _ = (0, 2147483562)
  split (MkStdGen s1 s2) =
    let gen' : StdGen = fst (next (MkStdGen s1 s2)) in
    let t1 : BaseGenTy = case gen' of { MkStdGen a b => a } in
    let t2 : BaseGenTy = case gen' of { MkStdGen a b => b } in
    let new_s1 : BaseGenTy = if s1 >= 2147483562 || s1 < 1
                         then 1
                         else s1 + 1 in
    let new_s2 : BaseGenTy = if s2 <= 1 || s2 >= 2147483398
                         then 2147483398
                         else s2 - 1 in
    let left : StdGen = MkStdGen (new_s1 - 1) t2 in
    let right : StdGen = MkStdGen t1 (new_s2 + 1) in
    (left, right)

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
                           else case (f n 1 gen) of
                             (gen', v) => (gen', (lo + v `mod` k))
    where
      k : BaseGenTy
      k = hi - lo + 1
      -- ERROR: b here (2^31-87) represents a baked-in assumption about genRange:
      b : BaseGenTy
      b = 2147483561

      iLogBase : BaseGenTy -> BaseGenTy
      iLogBase i = if i < b then 1 else 1 + iLogBase (assert_smaller i (i `div` b))

      n : BaseGenTy
      n = iLogBase k

      -- Here we loop until we've generated enough randomness to cover the range:
      f : BaseGenTy -> BaseGenTy -> g -> (g, BaseGenTy)
      f 0 acc g = (g, acc)
      f n' acc g =
        let (g',x) = next g in
        -- We shift over the random bits generated thusfar (* b) and add in the new ones.
        f (assert_smaller n' $ n' - 1) (x + acc * b) g'

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
