import Data.SortedBinTree.Gen
import Data.Fuel
import Data.List
import Data.List.Lazy
import Data.Primitives.Interpolation

import System.Random.Pure.StdGen

%default total

main : IO ()
main = do
  let vals = unGenTryN 10 someStdGen $ genSortedBinTree $ limit 5
  Lazy.for_ vals $ \tree => do
    putStrLn "--------------"
    let list = toList tree
    putStrLn "length: \{length list}"
    putStrLn "tree:\n\{tree}"
    putStrLn "as list: \{show list}"
    putStrLn "sorted: \{show $ sorted list}"
