module Main

import Test.Golden

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = testsInDir dir (const True) poolName [] Nothing

main : IO ()
main = runner
  [ !("PIL usage examples" `atDir` "pil")
  , !("Generators for PIL" `atDir` "gens")
  ]
