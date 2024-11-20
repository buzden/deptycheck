module Test

import Language.PilDyn.Derived.OutsGiven

import System.Random.Pure.StdGen

%default total

main : IO ()
main = do
  putStrLn "Output register state is given"
  let vals = unGenTryN 10 someStdGen $ genLinBlock'_ (limit 6) [Just I, Nothing, Just B, Just I]
  Lazy.for_ vals $ \lb => putStr """
    -------------------------
    \{lb}
    """
