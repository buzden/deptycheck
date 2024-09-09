module UseGen

import Data.List.Lazy

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

%cg chez lazy=weakMemo

guard : Bool -> Gen0 ()
guard True  = pure ()
guard False = empty

fun : Gen0 $ List Int
fun = do
  let nums = elements [1 .. 100]
  a <- nums
  b <- nums
  guard $ a == b
  c <- nums
  guard $ a == c
  d <- nums
  guard $ a == d
  e <- nums
  guard $ a == e
  f <- nums
  guard $ a == f
  pure [a, b, c, d, e, f]

main : IO Unit
main = Lazy.traverse_ printLn $ unGenTryN 10 someStdGen fun
