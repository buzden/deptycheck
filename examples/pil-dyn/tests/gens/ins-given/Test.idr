module Test

import Language.PilDyn.Derived.InsGiven

import System.Random.Pure.StdGen

%default total

main : IO ()
main = do
  putStrLn "Input registers state is given"
  let vals = unGenTryN 10 someStdGen $ genLinBlock_' (limit 6) [Just I, Nothing, Just B, Just I]
  Lazy.for_ vals $ \lb => putStr """
    -------------------------
    \{lb}
    """
