# Mastering Generator Control: Tuning Constructor Probabilities

## What We'll Accomplish
In this tutorial, we'll learn how to control which constructors appear more frequently in our generated test data. By the end, you'll:
- Understand default constructor probability distribution
- Use `ProbabilityTuning` to bias generation toward specific constructors
- Create custom probability distributions for targeted testing
- Have a working example demonstrating probability tuning

## Prerequisites
Before we begin, make sure you have:
- Completed the "Generate Test Data for a Simple Type with `deriveGen`" tutorial
- Idris 2 installed and DepTyCheck available in your project
- Basic familiarity with Idris syntax and data types

## Step 1: Observe Default Distribution

Let's start by seeing how DepTyCheck distributes constructor probabilities by default. Create a new file called `ProbabilityControl.idr`:

```idris
module ProbabilityControl

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.SortedMap
import Data.String

%language ElabReflection

data TrafficLight = Red | Yellow | Green

genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
genTrafficLight = deriveGen

countConstructors : List TrafficLight -> SortedMap String Nat
countConstructors = foldl (\acc, x => 
  let name = show x in
  mapUpdate (\c => Just (c + 1)) 1 name acc
) empty

main : IO ()
main = do
  putStrLn "Testing default constructor distribution:"
  let results = take 300 $ unGen1 (limit 100) genTrafficLight
  let counts = countConstructors results
  
  putStrLn "Constructor counts:"
  for_ (SortedMap.toList counts) $ \(name, count) =>
    putStrLn $ "  " ++ name ++ ": " ++ show count
```

**Expected result**: You should see roughly equal counts for Red, Yellow, and Green (around 100 each).

**What to notice**: DepTyCheck defaults to equal probability for all constructors.

## Step 2: Implement Probability Tuning

Now let's make Red appear more frequently and Yellow less frequently. Add the probability tuning instances:

```idris
-- Add to your existing file
import Deriving.DepTyCheck.Gen.Tuning
import Data.Nat1

instance ProbabilityTuning "Red".dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = fromInteger 5  -- Make Red 5x more likely

instance ProbabilityTuning "Yellow".dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = fromInteger 1  -- Keep Yellow at default

testTunedDistribution : IO ()
testTunedDistribution = do
  putStrLn "Testing tuned constructor distribution:"
  let results = take 300 $ unGen1 (limit 100) genTrafficLight
  let counts = countConstructors results
  
  putStrLn "Constructor counts after tuning:"
  for_ (SortedMap.toList counts) $ \(name, count) =>
    putStrLn $ "  " ++ name ++ ": " ++ show count

main : IO ()
main = do
  putStrLn "Testing default constructor distribution:"
  let results = take 300 $ unGen1 (limit 100) genTrafficLight
  let counts = countConstructors results
  
  putStrLn "Constructor counts:"
  for_ (SortedMap.toList counts) $ \(name, count) =>
    putStrLn $ "  " ++ name ++ ": " ++ show count
  
  putStrLn "\n"
  testTunedDistribution
```

**Expected result**: You should see significantly more Red values (around 200-250), with Yellow and Green sharing the remaining counts.

**What to notice**: The `tuneWeight` function lets us control relative constructor probabilities.

## Step 3: Apply Tuning to Complex Types

Let's apply probability tuning to a recursive data type to see how it affects generation:

```idris
-- Add to your existing file
data Tree a = Leaf a | Node (Tree a) (Tree a)

genTree : Fuel -> Gen MaybeEmpty (Tree Nat)
genTree = deriveGen

instance ProbabilityTuning "Leaf".dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = fromInteger 3  -- Make Leaf more likely

instance ProbabilityTuning "Node".dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = fromInteger 1  -- Keep Node at default

testTreeDistribution : IO ()
testTreeDistribution = do
  putStrLn "Testing tree constructor distribution:"
  let results = take 50 $ unGen1 (limit 5) genTree
  
  let leafCount = length $ filter (\case Leaf _ => True; _ => False) results
  let nodeCount = length $ filter (\case Node _ _ => True; _ => False) results
  
  putStrLn $ "Leaf count: " ++ show leafCount
  putStrLn $ "Node count: " ++ show nodeCount

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\nTesting tree constructor distribution:"
  testTreeDistribution
```

**Expected result**: You should see more Leaf constructors than Node constructors in the generated trees.

**What to notice**: Probability tuning works with recursive types and affects the overall structure of generated data.

## What We Accomplished

Congratulations! We've successfully learned how to control constructor probabilities:
- Observed default equal distribution
- Implemented custom probability tuning
- Applied tuning to both simple and complex types

You now have the power to bias your test data generation toward specific scenarios, making your property tests more targeted and effective.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Controlling Argument Generation Order
- How-to: Testing Edge Cases with Biased Generation
- Explanation: How Probability Tuning Affects Test Coverage

Or experiment by creating extreme probability distributions to test specific edge cases.