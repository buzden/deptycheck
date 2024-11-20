module Test

import Language.PilDyn.Derived.AllGiven

import System.Random.Pure.StdGen

%default total

main : IO ()
main = do
  putStrLn "Both inputs and outputs are given"
  let vals = unGenTryN 10 someStdGen $ genLinBlock__ (limit 6) [Just I, Nothing, Just B, Just I] [Just B, Just I, Just B, Just B]
  Lazy.for_ vals $ \lb => putStr """
    -------------------------
    \{lb}
    """
