module CheckDistribution

import Data.List.Sorted.Gen

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict (genSortedList $ limit depth) $ fromList
                  $ [ coverWith (ratio 1 $ S depth) ((== n) . length) | n <- [0 .. depth] ]

main : IO ()
main = do
  mainFor 2
  mainFor 5
  mainFor 10
