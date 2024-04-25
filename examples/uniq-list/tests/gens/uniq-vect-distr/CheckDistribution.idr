module CheckDistribution

import Data.Fuel
import Data.Vect.Uniq.Gen

import DistrCheckCommon

%default total

index : Fin n -> UniqStrVect n -> String
index FZ     (x::_ ) = x
index (FS k) (_::xs) = index k xs

strs : Nat -> Gen MaybeEmpty String
strs n = elements $ show <$> [0 .. n]

-- Check that every number in every position is uniformly distributed

-- insufficient for generation if `strsCnt < len`
mainFor : (len : Nat) -> (strsCnt : Nat) -> IO ()
mainFor len strsCnt = printVerdict (genUniqStrVect @{const $ strs strsCnt} (limit $ len * 2) len) $ fromList
                        [ coverWith (ratio 1 (S strsCnt)) ((== n) . index idx) | n <- show <$> [0 .. strsCnt], idx <- allFins len ]

-- NOTE: A separate test is when for this derived generator we pass `depth` test.
--       Now, since we still spend fuel even when `given` argument descreases, when we set high `len` > `depth`,
--       no statistics can be searched for.

main : IO ()
main = do
  mainFor 1 4 -- trivial, subgen check
  mainFor 7 5 -- not sufficient
  mainFor 4 4 -- tight
  mainFor 4 6 -- excess
