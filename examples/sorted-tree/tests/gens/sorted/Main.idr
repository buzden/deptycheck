import Data.SortedBinTree.Gen
import Data.Fuel
import Data.List
import Data.List.Lazy

import System.Random.Pure.StdGen

%default total

main : IO ()
main = do
  let vals = unGenTryN 10 someStdGen $ genSortedBinTree $ limit 6
  Lazy.for_ vals $ putStrLn . show . sorted . toList
