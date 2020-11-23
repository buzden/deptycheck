-- This is based on the David Christianen's port of QuickCheck to Idris 1

module Example.Random

import Data.Fin

%default total

--------------------------------
--- Interface for seed types ---
--------------------------------

public export
interface RandomGen g where
  next : g -> (Int, g)
  genRange : g -> (Int,Int)
  split : g -> (g, g)

--------------------------------
--- Example of the seed type ---
--------------------------------

export
data StdGen = MkStdGen Int Int

export
Show StdGen where
  show (MkStdGen i j) = "MkStdGen " ++ show i ++ " " ++ show j

-- Blatantly stolen from Haskell
export
RandomGen StdGen where
  next (MkStdGen s1 s2) =
    let k : Int = s1 `div` 53668 in
    let s1' : Int  = 40014 * (s1 - k * 53668) - k * 12211 in
    let s1'' : Int = if s1' < 0 then s1' + 2147483563 else s1' in
    let k' : Int = s2 `div` 52774 in
    let s2' : Int = 40692 * (s2 - k' * 52774) - k' * 3791 in
    let s2'' : Int = if s2' <= 0 then s2' + 2147483399 else s2' in
    let z : Int = s1'' - s2'' in
    let z' : Int = if z < 1 then z + 2147483562 else z in
    (z', MkStdGen s1'' s2'')

  genRange _ = (0, 2147483562)
  split (MkStdGen s1 s2) =
    let gen' : StdGen = snd (next (MkStdGen s1 s2)) in
    let t1 : Int = case gen' of { MkStdGen a b => a } in
    let t2 : Int = case gen' of { MkStdGen a b => b } in
    let new_s1 : Int = if s1 >= 2147483562 || s1 < 1
                         then 1
                         else s1 + 1 in
    let new_s2 : Int = if s2 <= 1 || s2 >= 2147483398
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
  randomR : RandomGen g => (a, a) -> g -> (a, g)
  random : RandomGen g => g -> (a, g)

--- Random Int ---

export
Random Int where
  random gen = next gen
  randomR (lo, hi) gen = if lo > hi
                           then assert_total $ randomR (hi, lo) gen
                           else case (f n 1 gen) of
                             (v, gen') => ((lo + v `mod` k), gen')
    where
      k : Int
      k = hi - lo + 1
      -- ERROR: b here (2^31-87) represents a baked-in assumption about genRange:
      b : Int
      b = 2147483561

      iLogBase : Int -> Int
      iLogBase i = if i < b then 1 else 1 + iLogBase (assert_smaller i (i `div` b))

      n : Int
      n = iLogBase k

      -- Here we loop until we've generated enough randomness to cover the range:
      f : Int -> Int -> g -> (Int, g)
      f 0 acc g = (acc, g)
      f n' acc g =
        let (x,g') = next g in
        -- We shift over the random bits generated thusfar (* b) and add in the new ones.
        f (assert_smaller n' $ n' - 1) (x + acc * b) g'

--- Random Nat ---

intToNat : Int -> Nat
intToNat = fromInteger . cast

export
Random Nat where
  randomR (lo, hi) = mapFst intToNat . randomR (cast lo, cast hi)
  random = mapFst intToNat . random

--- Random Unit ---

export
Random Unit where
  randomR ((), ()) gen = ((), snd $ next gen)
  random gen = ((), snd $ next gen)

--- Random Fin ---

finToInt : Fin n -> Int
finToInt = fromInteger . cast

intToFin : (n : Nat) -> Int -> Fin (S n)
intToFin n = restrict n . cast

export
{n : Nat} -> Random (Fin (S n)) where
  randomR (lo, hi) gen = mapFst (intToFin n) $ randomR (finToInt lo, finToInt hi) gen
  random = mapFst (intToFin n) . random

--- Random Char ---

export
Random Char where
  randomR (lo, hi) = mapFst chr . randomR (ord lo, ord hi)
  random = mapFst chr . random

--- Random Bool ---

boolToInt : Bool -> Int
boolToInt True = 1
boolToInt False = 0

intToBoolUni : Int -> Bool
intToBoolUni x = x `mod` 2 == 0

export
Random Bool where
  randomR (lo, hi) = mapFst intToBoolUni . randomR (boolToInt lo, boolToInt hi)
  random = mapFst intToBoolUni . random
