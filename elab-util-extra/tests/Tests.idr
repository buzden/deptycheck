module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner $
  [ "TTImp equality up to renaming" `atDir` "up-to-renaming-ttimp-eq"
  , "Getting argument dependencies" `atDir` "arg-deps"
  , "Analysing involved types"      `atDir` "involved-types"
  , "Typecheck Unifier"             `atDir` "typecheck-unifier"
  , "Monomorphiser"                 `atDir` "monomorphiser"
  ]
