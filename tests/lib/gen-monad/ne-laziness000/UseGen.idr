module UseGen

import Debug.Trace

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

g : Gen1 Nat
g = trace "--- outmost gen ---" $ oneOf
  [ pure $ trace "pure 6" 6
  ]

main : IO Unit
main = putStrLn $ show $ take 10 $ unGenAll someStdGen g
