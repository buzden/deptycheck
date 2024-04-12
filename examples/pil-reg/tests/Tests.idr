module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "PIL usage examples" `atDir` "lang"
  , "Generators for PIL" `atDir` "gens"
  ]
