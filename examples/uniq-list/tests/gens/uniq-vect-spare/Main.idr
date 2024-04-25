import Data.Fuel
import Data.List
import Data.List.Lazy
import Data.Vect
import Data.Vect.Uniq.Gen

import System.Random.Pure.StdGen

%default total

%hint
genStr : Gen MaybeEmpty String
genStr = elements ["a", "b", "c", "d", "f", "g", "h"]

main : IO ()
main = do
  putStrLn "prenty of spare strings to generate from (7 for vects of length 4)"
  let vals = unGenTryN 10 someStdGen $ genUniqStrVect (limit 8) 4
  Lazy.for_ vals $ \uv => do
    let ll = toList $ Uniq.toVect uv
    putStrLn """
      -----------
      vect: \{show ll}
      uniq: \{show $ ll == nub ll}
      """
