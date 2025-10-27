module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner $
  [ "The `Gen` monad" `atDir` "lib/gen-monad"
  , "Distribution of generators" `atDir` "lib/distribution"
  , "Model coverage" `atDir` "lib/coverage"
  , "John Hughes-style tests" `atDir` "lib/john-hughes"
  , "The library documentation" `atDir` "docs"
  , "Derivation utils: canonic signature" `atDir` "derivation/utils/canonicsig"
  , "Derivation utils: constructors analysis" `atDir` "derivation/utils/cons-analysis"
  , "Derivation utils: order tuning" `atDir` "derivation/utils/order-tuning"
  , "Derivation utils: specialise if needed" `atDir` "derivation/utils/specialise-if-needed"
  , "Derivation: input validation" `atDir` "derivation/inputvalidation"
  , "Derivation: running harness" `atDir` "derivation/infra"
  , [ "Derivation: least effort (\{p}, \{w})" `atDir` "derivation/least-effort/\{p}/\{w}"
    | p <- ["print", "run"], w <- ["adt", "gadt", "john-hughes", "order", "regression", "specialise"]
    ]
  , "Derivation: core" `atDir` "derivation/core"
  , "Derivation: distribution" `atDir` "derivation/distribution"
  ]
