module Test

import Language.PilDyn

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%hint
ints : Gen MaybeEmpty Int32
ints = elements [0..99]

genLinBlock__ : Fuel -> (Fuel -> Gen MaybeEmpty Int32) => {r : _} -> (ins, outs : Regs r) -> Gen MaybeEmpty $ LinBlock ins outs
genLinBlock__ = deriveGen

main : IO ()
main = do
  putStrLn "No register state is given"
  let vals = unGenTryN 10 someStdGen $ genLinBlock__ (limit 6) [Just I, Nothing, Just B, Just I] [Just B, Just I, Just B, Just B]
  Lazy.for_ vals $ \lb => putStr """
    -------------------------
    \{lb}
    """
