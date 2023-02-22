module Main

import Test.Golden

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = testsInDir dir (const True) poolName [] Nothing

