module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Sorted list data structure" `atDir` "data"
  , "Generator for lists with unique elements" `atDir` "gens"
  ]
