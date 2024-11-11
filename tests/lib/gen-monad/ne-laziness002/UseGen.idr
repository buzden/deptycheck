module UseGen

import Debug.Trace

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

g : Gen1 Nat
g = trace "--- outmost gen ---" $ oneOf
  [ oneOf $ trace "list with pure 4 and 5"
      [ pure $ trace "pure 4" 4
      , pure $ trace "pure 5" 5
      ]
  , pure $ trace "pure 6" 6
  ]

main : IO Unit
main = putStrLn $ show $ take 10 $ unGenAll someStdGen g
