module Runner

import BaseDir

import Test.Golden.RunnerHelper

RunScriptArg where
  runScriptArg = baseTestsDir ++ "/.pack_lock"

main : IO ()
main = goldenRunner $
  [ "Facilities for random generation" `atDir` "lib/random"
  , "The `Gen` monad" `atDir` "lib/gen-monad"
  , "Distribution of generators" `atDir` "lib/distribution"
  , "The library documentation" `atDir` "docs"
  , "Auto derivation: infrastructure: input validation" `atDir` "gen-derivation/inputvalidation"
  , "Auto derivation: infrastructure: TTImp equality up to renaming" `atDir` "gen-derivation/up-to-renaming-ttimp-eq"
  , "Auto derivation: infrastructure: canonic signature" `atDir` "gen-derivation/canonicsig"
  , "Auto derivation: infrastructure: constructors analysis" `atDir` "gen-derivation/cons-analysis"
  , "Auto derivation: infrastructure: running harness" `atDir` "gen-derivation/derivation/infra"
  , "Auto derivation: infrastructure: argument dependencies" `atDir` "gen-derivation/arg-deps"
  , [ "Auto derivation: core: cons: least effort (\{p}, \{w})" `atDir` "gen-derivation/derivation/least-effort/\{p}/\{w}"
    | p <- ["print", "run"], w <- ["adt", "gadt", "regression"]
    ]
  , "Auto derivation: core: derivation itself" `atDir` "gen-derivation/derivation/core"
  ]
