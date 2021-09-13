module RunDerivedGen

import DerivedGen

%default total

%hint
smallStrings : Fuel -> Gen String
smallStrings _ = choiceMap pure ["", "a", "bc"]

%hint
smallNats : Fuel -> Gen Nat
smallNats _ = choiceMap pure [0, 10]

%hint
someTypes : Fuel -> Gen Type
someTypes _ = choiceMap pure [Nat, String, Bool]

main : IO Unit
main = do
  putStrLn "Generated values:"
  traverse_ ((putStrLn "-----" >>) . putStrLn) $ map show $
    evalState someStdGen $ unGen $ derivedGen $ limit 20
