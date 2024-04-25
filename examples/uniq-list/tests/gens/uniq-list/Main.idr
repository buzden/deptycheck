import Data.Fuel
import Data.List
import Data.List.Lazy
import Data.List.Uniq.Gen

import System.Random.Pure.StdGen

%default total

%hint
genStr : Gen MaybeEmpty String
genStr = elements ["a", "b", "c", "d", "f", "g", "h"]

main : IO ()
main = do
  let vals = unGenTryN 10 someStdGen $ genUniqStrList $ limit 8
  Lazy.for_ vals $ \ul => do
    let ll = Uniq.toList ul
    putStrLn """
      -----------
      list: \{show ll}
      uniq: \{show $ ll == nub ll}
      """
