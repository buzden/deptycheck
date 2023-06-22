module Runner

import BaseDir

import Test.Golden.RunnerHelper

RunScriptArg where
  runScriptArg = baseTestsDir ++ "/.pack_lock"

main : IO ()
main = goldenRunner
  [ "PIL usage examples" `atDir` "pil"
  , "Generators for PIL" `atDir` "gens"
  ]
