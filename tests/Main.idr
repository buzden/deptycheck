module Main

import Data.String

import Test.Golden

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = testsInDir dir (not . isPrefixOf "_") poolName [] Nothing

main : IO ()
main = runner
  [ !("Lazier list" `atDir` "lazier")
  , !("The `Gen` monad" `atDir` "gen-monad")
  , !("Auto derivation: infrastructure: input validation" `atDir` "gen-derivation/inputvalidation")
  , !("Auto derivation: infrastructure: canonic signature" `atDir` "gen-derivation/canonicsig")
  , !("Auto derivation: infrastructure: running harness" `atDir` "gen-derivation/derivation/infra")
  , !("Auto derivation: infrastructure: argument dependencies" `atDir` "gen-derivation/arg-deps")
  , !("Auto derivation: core: derivation itself" `atDir` "gen-derivation/derivation/core")
  ]
