-- This is based on the David Christianen's port of QuickCheck to Idris 1

module System.Random.Simple

import Control.Monad.State

import Data.Fin

%default total

--------------------------------
--- Interface for seed types ---
--------------------------------

public export
interface RandomGen g where
  next : g -> (g, Int)
  genRange : g -> (Int,Int)
  split : g -> (g, g)

--------------------------------
--- Example of the seed type ---
--------------------------------

export
data StdGen = MkStdGen Int Int

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
    let k : Int = s1 `div` 53668 in
    let s1' : Int  = 40014 * (s1 - k * 53668) - k * 12211 in
    let s1'' : Int = if s1' < 0 then s1' + 2147483563 else s1' in
    let k' : Int = s2 `div` 52774 in
    let s2' : Int = 40692 * (s2 - k' * 52774) - k' * 3791 in
    let s2'' : Int = if s2' <= 0 then s2' + 2147483399 else s2' in
    let z : Int = s1'' - s2'' in
    let z' : Int = if z < 1 then z + 2147483562 else z in
    (MkStdGen s1'' s2'', z')

  genRange _ = (0, 2147483562)
  split (MkStdGen s1 s2) =
    let gen' : StdGen = fst (next (MkStdGen s1 s2)) in
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
  randomR : RandomGen g => (a, a) -> g -> (g, a)
  random : RandomGen g => g -> (g, a)

  -- `Nothing` for infinite or unknown
  cardinality : Maybe Nat
  cardinalityR : (a, a) -> Maybe Nat

export
randomR' : Random a => RandomGen g => (a, a) -> State g a
randomR' bounds = ST $ pure . randomR bounds

export
random' : Random a => RandomGen g => State g a
random' = ST $ pure . random

export
[RandomThru] Random thru => Cast a thru => Cast thru a => Random a where
  randomR (lo, hi) = map cast . randomR {a=thru} (cast lo, cast hi)
  random = map cast . random {a=thru}

  cardinality = cardinality {a=thru}
  cardinalityR (lo, hi) = cardinalityR {a=thru} (cast lo, cast hi)

--- Random Int ---

export
Random Int where
  random gen = next gen
  randomR (lo, hi) gen = if lo > hi
                           then assert_total $ randomR (hi, lo) gen
                           else case (f n 1 gen) of
                             (gen', v) => (gen', (lo + v `mod` k))
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
      f : Int -> Int -> g -> (g, Int)
      f 0 acc g = (g, acc)
      f n' acc g =
        let (g',x) = next g in
        -- We shift over the random bits generated thusfar (* b) and add in the new ones.
        f (assert_smaller n' $ n' - 1) (x + acc * b) g'

  cardinality = Nothing
  cardinalityR (a, b) = Just $ cast $ if a > b then a - b else b - a

--- Random Nat ---

export %hint
RandomNat : Random Nat
RandomNat = RandomThru {thru=Int}

--- Random Unit ---

export
Random Unit where
  randomR ((), ()) gen = map (const ()) $ next gen
  random gen = map (const ()) $ next gen

  cardinality = Just 1
  cardinalityR _ = Just 1

--- Random Fin ---

finToInt : Fin n -> Int
finToInt = fromInteger . cast

intToFin : (n : Nat) -> Int -> Fin (S n)
intToFin n = restrict n . cast

export
{n : Nat} -> Random (Fin (S n)) where
  randomR (lo, hi) = map (intToFin n) . randomR (finToInt lo, finToInt hi)
  random = map (intToFin n) . random

  cardinality = Just n
  cardinalityR (a, b) = cardinalityR (finToInt a, finToInt b)

--- Random Char ---

export %hint
RandomChar : Random Char
RandomChar = RandomThru {thru=Int}

--- Random Bool ---

boolToInt : Bool -> Int
boolToInt True = 1
boolToInt False = 0

intToBoolUni : Int -> Bool
intToBoolUni x = x `mod` 2 == 0

export
Random Bool where
  randomR (lo, hi) = map intToBoolUni . randomR (boolToInt lo, boolToInt hi)
  random = map intToBoolUni . random

  cardinality = Just 2
  cardinalityR (a, b) = if a == b then Just 1 else Just 2
