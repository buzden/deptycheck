module UseGen

import Data.List.Lazy

import Debug.Trace

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.NonEmpty

import System.Random.Pure.StdGen

%default total

g : Gen Nat
g = trace "--- outmost gen ---" $ oneOf
  [ fromNonEmpty $ pure $ trace "<ne> pure 6" 6
  , pure $ trace "pure 5" 5
  ]

main : IO Unit
main = putStrLn $ show $ unGenTryN 10 someStdGen g
