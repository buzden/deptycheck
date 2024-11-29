module CheckDistribution

import Data.SortedBinTree.Gen

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%language ElabReflection

-- Check how weights of subtrees are related between left and right subtree of a root

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict (genSortedBinTree1 $ limit depth) $ fromList
                  $ [ coverWith (ratio 1 $ S depth) ((== n) . length) | n <- [0 .. depth] ]

main : IO ()
main = do
  mainFor 0
  mainFor 1
  mainFor 2
  mainFor 7
