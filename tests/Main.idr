module Main

import Data.String

import Test.Golden

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = testsInDir dir (not . isPrefixOf "_") poolName [] Nothing

main : IO ()
main = runner
  [ !("Lazier list" `atDir` "lib/lazier")
  , !("The `Gen` monad" `atDir` "lib/gen-monad")
  , !("The library documentation" `atDir` "docs")
  , !("Auto derivation: infrastructure: input validation" `atDir` "gen-derivation/inputvalidation")
  , !("Auto derivation: infrastructure: canonic signature" `atDir` "gen-derivation/canonicsig")
  , !("Auto derivation: infrastructure: constructors analysis" `atDir` "gen-derivation/cons-analysis")
  , !("Auto derivation: infrastructure: running harness" `atDir` "gen-derivation/derivation/infra")
  , !("Auto derivation: infrastructure: argument dependencies" `atDir` "gen-derivation/arg-deps")
  , !("Auto derivation: core: cons: least effort" `atDir` "gen-derivation/derivation/least-effort")
  , !("Auto derivation: core: derivation itself" `atDir` "gen-derivation/derivation/core")
  ]
