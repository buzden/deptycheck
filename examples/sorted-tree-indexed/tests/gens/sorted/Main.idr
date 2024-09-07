import Data.SortedBinTree.Gen
import Data.Fuel
import Data.List
import Data.List.Lazy
import Data.Primitives.Interpolation

import System.Random.Pure.StdGen

%default total

main : IO ()
main = do
  let vals = unGenTryN 10 someStdGen $ genSortedBinTree1 $ limit 4
  Lazy.for_ vals $ \(mi ** ma ** tree) => do
    putStrLn "--------------"
    let list = toList tree
    putStrLn "min: \{mi}, max: \{ma}, length: \{length list}"
    putStrLn "tree:\n\{tree}"
    putStrLn "as list: \{show list}"
    putStrLn "sorted: \{show $ sorted list}"
