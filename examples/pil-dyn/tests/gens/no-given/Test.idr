module Test

import Language.PilDyn

import Deriving.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%hint
ints : Gen MaybeEmpty Int32
ints = elements [0..99]

genLinBlock'' : Fuel -> (Fuel -> Gen MaybeEmpty Int32) => (r : _) -> Gen MaybeEmpty (ins : Regs r ** outs : Regs r ** LinBlock ins outs)
genLinBlock'' = deriveGen

main : IO ()
main = do
  putStrLn "No register state is given"
  let vals = unGenTryN 10 someStdGen $ genLinBlock'' (limit 6) 4
  Lazy.for_ vals $ \lb => putStr """
    -------------------------
    \{lb}
    """
