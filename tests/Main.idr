module Main

import Test.Golden

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = testsInDir dir (const True) poolName [] Nothing

main : IO ()
main = runner
  [ !("Lazier list" `atDir` "lazier")
  , !("The `Gen` monad" `atDir` "gen-monad")
  , !("Derivation of `Gen`s" `atDir` "auto-gen")
  ]
