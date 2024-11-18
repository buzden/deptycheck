module Test

import Language.PilDyn

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%hint
ints : Gen MaybeEmpty Int32
ints = elements [0..99]

genLinBlock'_ : Fuel -> (Fuel -> Gen MaybeEmpty Int32) => {r : _} -> (outs : Regs r) -> Gen MaybeEmpty (ins : Regs r ** LinBlock ins outs)
genLinBlock'_ = deriveGen

main : IO ()
main = do
  putStrLn "No register state is given"
  let vals = unGenTryN 10 someStdGen $ genLinBlock'_ (limit 6) [Just I, Nothing, Just B, Just I]
  Lazy.for_ vals $ \lb => putStr """
    -------------------------
    \{lb}
    """
