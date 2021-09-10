module RunDerivedGen

import DerivedGen

%default total

%hint
smallStrings : Fuel -> Gen String
smallStrings _ = oneOf $ pure <$> ["", "a", "bc"]

%hint
smallNats : Fuel -> Gen Nat
smallNats _ = oneOf $ pure <$> [0, 10]

main : IO Unit
main = do
  putStrLn "Generated values:"
  traverse_ ((putStrLn "-----" >>) . putStrLn) $ map show $
    evalState someStdGen $ unGen $ derivedGen $ limit 20
