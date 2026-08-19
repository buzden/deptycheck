import Data.Fuel
import Data.List
import Data.List.Lazy
import Data.List.Sorted.Gen

import System.Random.Pure.StdGen

%default total

main : IO ()
main = do
  let vals = unGenTryN 10 someStdGen $ genSortedList $ limit 100
  Lazy.for_ vals $ putStrLn . show . sorted . toList
