module RunDerivedGen

import DerivedGen

%default total

main : IO Unit
main = do
  putStrLn "Generated values:"
  traverse_ ((putStrLn "-----" >>) . putStrLn) $ map show $
    evalState someStdGen $ unGen $ derivedGen $ limit 20
