module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Deep wide tree data structure" `atDir` "data"
  , "Generators for deep wide trees" `atDir` "gens"
  ]
