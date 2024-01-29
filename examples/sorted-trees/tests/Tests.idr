module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Sorted binary tree data structure" `atDir` "data"
  , "Generators for sorted binary trees" `atDir` "gens"
  ]
