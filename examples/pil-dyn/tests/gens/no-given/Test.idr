module Test

import Language.PilDyn.Derived.NoGiven

import System.Random.Pure.StdGen

%default total

main : IO ()
main = do
  putStrLn "No register state is given"
  let vals = unGenTryN 10 someStdGen $ genLinBlock'' (limit 6) 4
  Lazy.for_ vals $ \lb => putStr """
    -------------------------
    \{lb}
    """
