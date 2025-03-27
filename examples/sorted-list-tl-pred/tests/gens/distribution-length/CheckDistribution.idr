module CheckDistribution

import Data.List.Sorted.Gen

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%language ElabReflection

-- Check that lengths are uniformly distributed

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict (genSortedList $ limit depth) $ fromList
                  $  [ coverWith (ratio 1 $ S depth) ((== n) . length) | n <- [0 .. depth] ]

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 7
