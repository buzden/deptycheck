module Test

import Language.PilDyn

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%hint
ints : Gen MaybeEmpty Int32
ints = elements [0..99]

genLinBlock_' : Fuel -> (Fuel -> Gen MaybeEmpty Int32) => {r : _} -> (ins : Regs r) -> Gen MaybeEmpty (outs : Regs r ** LinBlock ins outs)
genLinBlock_' = deriveGen

main : IO ()
main = do
  putStrLn "No register state is given"
  let vals = unGenTryN 10 someStdGen $ genLinBlock_' (limit 6) [Just I, Nothing, Just B, Just I]
  Lazy.for_ vals $ \lb => putStr """
    -------------------------
    \{lb}
    """
