module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner $
  [ "TTImp equality up to renaming" `atDir` "up-to-renaming-ttimp-eq"
  , "Getting argument dependencies" `atDir` "arg-deps"
  , "Analysing involved types"      `atDir` "involved-types"
  , "Compiler-driven unification"   `atDir` "unify-with-compiler"
  , "Specify data"                  `atDir` "specify-data"
  ]
