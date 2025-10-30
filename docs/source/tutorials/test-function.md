# Getting Started: Test Your First Function with DepTyCheck

## What We'll Accomplish
In this tutorial, we'll create and test a simple function using property-based testing. By the end, you'll:
- Set up a basic DepTyCheck testing environment
- Create automatic generators for your data types
- Write and run property tests
- Understand the core testing workflow

## Prerequisites
Before we begin, make sure you have:
- Idris 2 installed
- Basic familiarity with Idris syntax
- The DepTyCheck library available in your project

## Step 1: Create Your Test Project

Let's start by creating a simple project structure. Create a new file called `FirstTest.idr`:

```idris
module FirstTest

import Data.List

%default total

data Person = MkPerson String Nat

sortByAge : List Person -> List Person
sortByAge = sortBy (compare `on` (case MkPerson _ age => age))

main : IO ()
main = putStrLn "Ready for testing!"
```

**Expected result**: You should have a basic file with a Person type and sorting function.

**What to notice**: We're creating a simple domain model to test.

## Step 2: Add DepTyCheck Dependencies

Now let's add the necessary imports for property testing:

```idris
-- Update FirstTest.idr
module FirstTest

import Data.List
import Data.Fuel
import Deriving.DepTyCheck.Gen
import Test.DepTyCheck.Gen

%default total
%language ElabReflection

data Person = MkPerson String Nat

sortByAge : List Person -> List Person
sortByAge = sortBy (compare `on` (case MkPerson _ age => age))

main : IO ()
main = putStrLn "Ready for testing!"
```

**Expected result**: Your file should compile with the new imports.

**What to notice**: We've added the core DepTyCheck modules and enabled reflection.

## Step 3: Create Automatic Generators

Let's use automatic derivation to create generators for our types:

```idris
-- Continue in FirstTest.idr

genPerson : Fuel -> Gen MaybeEmpty Person
genPerson = deriveGen

genPersonList : Fuel -> Gen MaybeEmpty (List Person)
genPersonList = deriveGen

testBasicGeneration : IO ()
testBasicGeneration = do
  putStrLn "Testing basic generation:"
  let people = take 3 $ unGen1 (limit 5) (genPerson (limit 5))
  let lists = take 3 $ unGen1 (limit 5) (genPersonList (limit 5))
  
  putStrLn "Individual people:"
  traverse_ (putStrLn . show) people
  
  putStrLn "\nLists of people:"
  traverse_ (putStrLn . show) lists

main : IO ()
main = do
  testBasicGeneration
```

**Expected result**: You should see generated Person values and lists.

**What to notice**: `deriveGen` automatically creates appropriate generators.

## Step 4: Write Your First Property Test

Now let's test our sorting function with properties:

```idris
-- Continue in FirstTest.idr

testSortingIdempotent : IO ()
testSortingIdempotent = do
  let gen = genPerson (limit 5)
  printVerdict gen
    [ coverWith 50.percent (\p => sortByAge [p, p] == [p, p])
    , coverWith 50.percent (\p => sortByAge (sortByAge [p]) == [p])
    ]

testSortingPreservesLength : IO ()
testSortingPreservesLength = do
  let gen = genPersonList (limit 5)
  printVerdict gen
    [ coverWith 100.percent (\people => length (sortByAge people) == length people)
    ]

testSortingOrder : IO ()
testSortingOrder = do
  let gen = genPersonList (limit 5)
  printVerdict gen
    [ coverWith 100.percent (\people => 
        let sorted = sortByAge people in
        case sorted of
          [] => True
          [_] => True
          p1 :: p2 :: _ => 
            let MkPerson _ age1 = p1
                MkPerson _ age2 = p2
            in age1 <= age2
      )
    ]

main : IO ()
main = do
  putStrLn "Testing sorting properties:"
  testSortingIdempotent
  testSortingPreservesLength
  testSortingOrder
```

**Expected result**: All tests should pass with coverage statistics.

**What to notice**: We're testing multiple properties of the sorting function.

## Step 5: Handle Edge Cases

Let's add tests for edge cases:

```idris
-- Continue in FirstTest.idr

testEmptyList : IO ()
testEmptyList = do
  let gen = pure []
  printVerdict gen
    [ coverWith 100.percent (\people => sortByAge people == [])
    ]

testSingleElement : IO ()
testSingleElement = do
  let gen = map (\p => [p]) (genPerson (limit 5))
  printVerdict gen
    [ coverWith 100.percent (\people => sortByAge people == people)
    ]

main : IO ()
main = do
  putStrLn "Testing sorting properties:"
  testSortingIdempotent
  testSortingPreservesLength
  testSortingOrder
  
  putStrLn "\nTesting edge cases:"
  testEmptyList
  testSingleElement
```

**Expected result**: Edge case tests should also pass.

**What to notice**: We're ensuring our function handles all scenarios correctly.

## Step 6: Run Your Complete Test Suite

Compile and run your tests:

```bash
idris2 --package deptycheck FirstTest.idr -o firsttest && ./firsttest
```

**You should see**: All tests passing with detailed coverage information.

## What We Accomplished

Congratulations! We've successfully created a complete property-based testing suite:
- Set up a DepTyCheck testing environment
- Created automatic generators for custom types
- Written comprehensive property tests
- Tested both normal behavior and edge cases

You now have the foundation to test any function with DepTyCheck.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Testing Recursive Data Structures
- How-to: Customizing Generator Behavior
- Explanation: Understanding Test Coverage Analysis

Or experiment by:
- Adding more properties to test different aspects
- Creating more complex data types to test
- Testing functions with different signatures