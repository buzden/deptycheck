module Main

import Data.String

import Test.Golden

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = testsInDir dir (not . isPrefixOf "_") poolName [] Nothing

main : IO ()
main = runner
  [ !("Lazier list" `atDir` "lazier")
  , !("The `Gen` monad" `atDir` "gen-monad")
  , !("Auto derivation: input validation" `atDir` "auto-gen/inputvalidation")
  , !("Auto derivation: internal functions" `atDir` "auto-gen/internal")
  ]
