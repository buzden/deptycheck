module Main

import Data.String

import Test.Golden

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = testsInDir dir (not . isPrefixOf "_") poolName [] Nothing

main : IO ()
main = runner
  [ !("Lazier list" `atDir` "lazier")
  , !("The `Gen` monad" `atDir` "gen-monad")
  , !("Auto derivation: input validation" `atDir` "gen-derivation/inputvalidation")
  , !("Auto derivation: internal canonic signature function" `atDir` "gen-derivation/canonicsig")
  , !("Auto derivation: derivation itself" `atDir` "gen-derivation/derivation")
  ]
