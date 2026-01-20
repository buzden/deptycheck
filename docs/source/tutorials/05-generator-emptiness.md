# Learning to Write Reliable Generators: Understanding Emptiness Guarantees

## What We'll Accomplish
In this tutorial, we'll learn how DepTyCheck helps you write reliable generators by understanding when generators can fail and when they're guaranteed to succeed. By the end, you'll:
- Create generators with different emptiness guarantees
- Understand when and why generators might produce no value
- Compose generators safely using type-level guarantees
- Have a working example demonstrating these concepts

## Prerequisites
Before we begin, make sure you have:
- Completed the "Generate Test Data for a Simple Type with `deriveGen`" tutorial
- Idris 2 installed and DepTyCheck available in your project
- Basic familiarity with Idris syntax and the Gen monad

## Step 1: Create a Guaranteed-Success Generator

Let's start by creating a generator that always produces a value. First, create a new file called `EmptinessLearning.idr`:

```idris
module EmptinessLearning

import Data.Fuel
import Test.DepTyCheck.Gen

%language ElabReflection

data Coin = Heads | Tails

genCoin : Fuel -> Gen NonEmpty Coin
genCoin = deriveGen

main : IO ()
main = do
  putStrLn "Testing our guaranteed generator:"
  let results = take 5 $ unGen1 (limit 10) genCoin
  traverse_ (putStrLn . show) results
```

**Expected result**: You should see 5 coin values (Heads or Tails). The generator will always produce results.

**What to notice**: The type `Gen NonEmpty Coin` guarantees this generator will always succeed given sufficient fuel.

## Step 2: Create a Generator That Might Fail

Now let's create a generator that might not always produce a value:

```idris
-- Add to your existing file
import Data.Maybe
import Data.List

genNonZeroNat : Fuel -> Gen MaybeEmpty Nat
genNonZeroNat fuel = suchThat (deriveGen {a=Nat}) (\n => n > 0)

testMaybeEmpty : IO ()
testMaybeEmpty = do
  putStrLn "Testing our maybe-empty generator:"
  let results = take 10 $ unGen1 (limit 3) genNonZeroNat
  putStrLn $ "Generated " ++ show (length (catMaybes results)) ++ " values out of 10 attempts"
  traverse_ (putStrLn . maybe "Nothing" show) results

main : IO ()
main = do
  putStrLn "Testing our guaranteed generator:"
  let results = take 5 $ unGen1 (limit 10) genCoin
  traverse_ (putStrLn . show) results
  
  putStrLn "\n" 
  testMaybeEmpty
```

**Expected result**: You'll see some numbers and possibly some "Nothing" results. The generator might fail due to the restrictive condition.

**What to notice**: `suchThat` changes the emptiness guarantee from `NonEmpty` to `MaybeEmpty`.

## Step 3: See Emptiness Propagation in Action

Let's observe how emptiness guarantees propagate when composing generators:

```idris
-- Add to your existing file
genCoinList : Fuel -> Gen MaybeEmpty (List Coin)
genCoinList = deriveGen

compositeGen : Fuel -> Gen MaybeEmpty (Coin, List Coin)
compositeGen fuel = do
  coin <- genCoin fuel
  coins <- genCoinList fuel
  pure (coin, coins)

testComposite : IO ()
testComposite = do
  putStrLn "Testing composite generator:"
  let results = take 3 $ unGen1 (limit 2) compositeGen
  traverse_ (putStrLn . maybe "Failed" show) results

main : IO ()
main = do
  putStrLn "Testing our guaranteed generator:"
  let results = take 5 $ unGen1 (limit 10) genCoin
  traverse_ (putStrLn . show) results
  
  putStrLn "\n" 
  testMaybeEmpty
  
  putStrLn "\nTesting composite generator:"
  testComposite
```

**Expected result**: You'll see tuples of (Coin, List Coin) or "Failed" if the list generator runs out of fuel.

**What to notice**: When we compose generators, the result inherits the weakest emptiness guarantee of its components.

## What We Accomplished

Congratulations! We've successfully learned how DepTyCheck's emptiness guarantees work:
- Created generators with different emptiness guarantees
- Observed how guarantees propagate through composition
- Understood when generators might fail and why

You now have practical experience with writing reliable generators and can apply these concepts to your own property tests.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Customizing Generator Distributions
- How-to: Handling Complex Dependent Types
- Explanation: How Emptiness Guarantees Prevent Bugs

Or experiment by modifying the `suchThat` condition to see how it affects generator reliability.