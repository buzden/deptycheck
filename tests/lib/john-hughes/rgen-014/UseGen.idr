module UseGen

import Data.List.Lazy

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%cg chez lazy=weakMemo

gen : Gen0 (Int, Int)
gen = do
  a <- elements [0 .. 100]
  guard $ a `mod` 20 == 0
  k <- elements [0 .. 100000]
  pure (a, k)

main : IO Unit
main = Lazy.traverse_ printLn $ unGenTryN 10 someStdGen gen
