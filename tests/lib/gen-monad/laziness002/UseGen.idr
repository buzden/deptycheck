module UseGen

import Data.List.Lazy

import Debug.Trace

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.NonEmpty

import System.Random.Pure.StdGen

%default total

g : Gen0 Nat
g = trace "--- outmost gen ---" $ oneOf
  [ oneOf $ trace "-- list with pure 4, 5, 6 --"
      [ pure $ trace "pure 4" 4
      , pure $ trace "pure 5" 5
      , pure $ trace "pure 6" 6
      ]
  , pure $ trace "pure 7" 7
  ]

main : IO Unit
main = putStrLn $ show $ unGenTryN 10 someStdGen g
