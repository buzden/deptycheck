module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Sorted list data structure" `atDir` "data"
  , "Generator for sorted lists" `atDir` "gens"
  ]
