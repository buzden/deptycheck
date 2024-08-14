module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Covering sequence data structure" `atDir` "data"
  , "Generator for covering sequences" `atDir` "gens"
  ]
