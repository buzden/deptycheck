module Main

import Data.String

import Test.Golden

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = testsInDir dir (not . isPrefixOf "_") poolName [] Nothing

main : IO ()
main = runner $
  [ !("Facilities for random generation" `atDir` "random")
  , !("The `Gen` monad" `atDir` "lib/gen-monad")
  , !("Distribution of generators" `atDir` "lib/distribution")
  , !("The library documentation" `atDir` "docs")
  , !("Auto derivation: infrastructure: input validation" `atDir` "gen-derivation/inputvalidation")
  , !("Auto derivation: infrastructure: TTImp equality up to renaming" `atDir` "gen-derivation/up-to-renaming-ttimp-eq")
  , !("Auto derivation: infrastructure: canonic signature" `atDir` "gen-derivation/canonicsig")
  , !("Auto derivation: infrastructure: constructors analysis" `atDir` "gen-derivation/cons-analysis")
  , !("Auto derivation: infrastructure: running harness" `atDir` "gen-derivation/derivation/infra")
  , !("Auto derivation: infrastructure: argument dependencies" `atDir` "gen-derivation/arg-deps")
  ] ++
  !(sequence [
    "Auto derivation: core: cons: least effort (\{p}, \{w})" `atDir` "gen-derivation/derivation/least-effort/\{p}/\{w}"
    | p <- ["print", "run"], w <- ["adt", "gadt", "regression"]
  ]) ++
  [ !("Auto derivation: core: derivation itself" `atDir` "gen-derivation/derivation/core")
  ]
