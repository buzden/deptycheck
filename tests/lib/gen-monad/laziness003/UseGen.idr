module UseGen

import Data.List.Lazy

import Debug.Trace

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

g : Gen CanBeEmptyStatic Nat
g = trace "--- outmost gen ---" $ oneOf
  [ oneOf $ trace "-- list with pure 4, 5 --"
      [ pure $ trace "pure 4" 4
      , pure $ trace "pure 5" 5
      , oneOf $ trace "- inner actually empty list -"
        [ trace "1st empty" empty
        , trace "2nd empty" empty
        , trace "3rd empty" empty
        , trace "4th empty" empty
        ]
      ]
  , pure $ trace "pure 7" 7
  ]

main : IO Unit
main = putStrLn $ show $ unGenTryN 10 someStdGen g
