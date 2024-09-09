module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner $
  [ "The `Gen` monad" `atDir` "lib/gen-monad"
  , "Distribution of generators" `atDir` "lib/distribution"
  , "Model coverage" `atDir` "lib/coverage"
  , "John Hughes-style tests" `atDir` "lib/john-hughes"
  , "The library documentation" `atDir` "docs"
  , "Derivation utils: TTImp equality up to renaming" `atDir` "derivation/utils/up-to-renaming-ttimp-eq"
  , "Derivation utils: canonic signature" `atDir` "derivation/utils/canonicsig"
  , "Derivation utils: constructors analysis" `atDir` "derivation/utils/cons-analysis"
  , "Derivation utils: argument dependencies" `atDir` "derivation/utils/arg-deps"
  , "Reflection utils: involved types" `atDir` "derivation/utils/involved-types"
  , "Derivation: input validation" `atDir` "derivation/inputvalidation"
  , "Derivation: running harness" `atDir` "derivation/infra"
  , [ "Derivation: least effort (\{p}, \{w})" `atDir` "derivation/least-effort/\{p}/\{w}"
    | p <- ["print", "run"], w <- ["adt", "gadt", "regression"]
    ]
  , "Derivation: core" `atDir` "derivation/core"
  , "Derivation: distribution" `atDir` "derivation/distribution"
  ]
