module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "The language" `atDir` "lang"
  , "Generators"   `atDir` "gens"
  ]
