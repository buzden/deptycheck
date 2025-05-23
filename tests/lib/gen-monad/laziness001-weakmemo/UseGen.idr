module UseGen

import Data.List.Lazy

import Debug.Trace

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%cg chez lazy=weakMemo

g : Gen MaybeEmpty Nat
g = trace "--- outmost gen ---" $ oneOf
  [ pure $ trace "pure 6" 6
  , pure $ trace "pure 5" 5
  ]

main : IO Unit
main = putStrLn $ show $ unGenTryN 10 someStdGen g
