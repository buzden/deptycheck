import Data.Fuel
import Data.List
import Data.List.Lazy
import Data.List.Covering.Gen
import Data.String

import System.Random.Pure.StdGen

%default total

submain : {n : _} -> BitMask n -> IO ()
submain bs = do
  putStrLn "-----------------------"
  putStrLn "bitmask: \{bs}"
  putStrLn "-----------------------"
  let vals = unGenTryN 10 someStdGen $ genCoveringSequence (limit $ 2 * n) bs
  Lazy.for_ vals $ \v => do
    let hits = hits v
    let verdict = if sort hits == setBits bs then "ok" else "fail, hits are: \{show hits}, expected: \{show $ setBits bs}"
    putStrLn "\{v} (\{verdict})"

main : IO ()
main = do
  submain [True, True, True, True]
  submain [True, False, True, True]
  submain [False, False, True, False]
  submain [False, False, False, False]
