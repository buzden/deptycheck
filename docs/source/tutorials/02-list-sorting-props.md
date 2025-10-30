# Property Testing a List Sorting Function

## Introduction

In this tutorial, we'll test a sorting function using property-based testing with DepTyCheck. You'll learn how to define properties that characterize correct sorting behavior and use automatic test data generation to verify these properties hold for thousands of random inputs.

By the end of this tutorial, you will have:
- A working property test for a sorting function
- Understanding of how to express software properties
- Experience running automated property tests
- Knowledge of interpreting test results

### What we'll build together
We'll create a property test suite that automatically generates random lists of numbers, sorts them, and verifies three key properties:
1. Length preservation (sorting doesn't change list length)
2. Correct ordering (output is actually sorted)
3. Element preservation (output contains same elements as input)

**Expected learning time**: 20-25 minutes

## Prerequisites

Before we begin, make sure you have:

- Completed Tutorial 1: "Generating Test Data for a Simple Type with `deriveGen`"
- Idris 2 and DepTyCheck installed and working
- Basic familiarity with list operations in Idris

## Step 1: Create the file and basic imports

Let's start by creating our test file and importing the necessary modules.

Create a new file called `SortingTest.idr` and add this code:

```idris
module SortingTest

%language ElabReflection

import Data.List
import Data.Nat
import Data.Fuel
import Test.DepTyCheck.Gen
```

**What to do**: Create the file and add these imports exactly as shown.

**Expected result**: You have a basic file structure ready for property testing.

**What you'll notice**: We're importing standard list operations and the DepTyCheck testing framework.

### Prerequisites
Before tackling this tutorial, please ensure you have:
- **Completed \"Generate Test Data for a Simple Type with `deriveGen`\"**: This tutorial builds directly on the foundational knowledge of `DepTyCheck` and `deriveGen`.
- Idris 2 installed and `DepTyCheck` set up in your project.
- Basic familiarity with Idris list manipulation and function definitions.

## Step 2: Define the function we want to test

Now let's define the sorting function we want to test. We'll use Idris's built-in sort function wrapped in our own function.

Add this to your `SortingTest.idr` file:

```idris
module SortingTest

%language ElabReflection

import Data.List
import Data.Nat
import Data.Fuel
import Test.DepTyCheck.Gen

-- Our function under test: sorts a list of natural numbers
sortNatList : List Nat -> List Nat
sortNatList = sort
```

**What to do**: Add the `sortNatList` function definition.

**Expected result**: Your file now contains a simple sorting function.

**What you'll notice**: We're wrapping the standard `sort` function - this is the "system under test" that we'll verify behaves correctly.

## Step 3: Create a generator for test data

Now we need a way to generate random lists of natural numbers to test our sorting function. DepTyCheck can automatically create this generator for us.

Add the generator definition to your file:

```idris
module SortingTest

%language ElabReflection

import Data.List
import Data.Nat
import Data.Fuel
import Test.DepTyCheck.Gen

sortNatList : List Nat -> List Nat
sortNatList = sort

-- Automatically derive a generator for List Nat
genNatList : Fuel -> Gen MaybeEmpty (List Nat)
genNatList = deriveGen
```

**What to do**: Add the `genNatList` function definition.

**Expected result**: Your file should compile without errors.

**What you'll notice**: The `deriveGen` macro automatically creates code that can generate random lists of natural numbers. The `Fuel` parameter controls how large the generated lists can be.

**Important**: Try compiling your file now to make sure everything works:
```bash
idris2 --check SortingTest.idr
```

You should see no errors if everything is correct.

## Step 4: Define properties of correct sorting

Property-based testing is about verifying that certain properties hold for all possible inputs, not just specific examples. Let's define three key properties that should always be true for a correct sorting function.

Add these property definitions to your file:

```idris
module SortingTest

%language ElabReflection

import Data.List
import Data.Nat
import Data.Fuel
import Test.DepTyCheck.Gen

sortNatList : List Nat -> List Nat
sortNatList = sort

genNatList : Fuel -> Gen MaybeEmpty (List Nat)
genNatList = deriveGen

-- Property 1: Sorting preserves list length
prop_lengthPreserved : List Nat -> Bool
prop_lengthPreserved xs = length (sortNatList xs) == length xs

-- Property 2: The output is actually sorted
prop_isSorted : List Nat -> Bool
prop_isSorted []       = True  -- Empty lists are sorted
prop_isSorted [_]      = True  -- Single-element lists are sorted
prop_isSorted (x :: y :: xs) = x <= y && prop_isSorted (y :: xs)

-- Property 3: The sorted list contains the same elements
-- We'll use sum as a simple check (not perfect but good for learning)
prop_isPermutation : List Nat -> Bool
prop_isPermutation xs = sum xs == sum (sortNatList xs)

-- Combine all properties into one test
allProps : List Nat -> Bool
allProps xs = prop_lengthPreserved xs &&
              prop_isSorted xs &&
              prop_isPermutation xs
```

**What to do**: Add these four property functions to your file.

**Expected result**: You now have complete definitions of what "correct sorting" means.

**What you'll notice**:
- Each property is a simple boolean function that checks one aspect of correctness
- `prop_lengthPreserved` ensures sorting doesn't change list size
- `prop_isSorted` recursively checks that elements are in order
- `prop_isPermutation` uses sum as a quick check for same elements
- `allProps` combines everything into a single test

**Try testing manually**: You can test these properties manually:
```idris
-- In Idris REPL, try:
> prop_lengthPreserved [3,1,2]
True
> prop_isSorted [1,2,3]
True
> prop_isSorted [3,1,2]
False
```

## Step 5: Run the property tests

Now we're ready to run our property tests automatically. DepTyCheck will generate thousands of random lists and verify our properties hold for all of them.

Add the final section to your file:

```idris
module SortingTest

%language ElabReflection

import Data.List
import Data.Nat
import Data.Fuel
import Test.DepTyCheck.Gen

sortNatList : List Nat -> List Nat
sortNatList = sort

genNatList : Fuel -> Gen MaybeEmpty (List Nat)
genNatList = deriveGen

prop_lengthPreserved : List Nat -> Bool
prop_lengthPreserved xs = length (sortNatList xs) == length xs

prop_isSorted : List Nat -> Bool
prop_isSorted []       = True
prop_isSorted [_]      = True
prop_isSorted (x :: y :: xs) = x <= y && prop_isSorted (y :: xs)

prop_isPermutation : List Nat -> Bool
prop_isPermutation xs = sum xs == sum (sortNatList xs)

allProps : List Nat -> Bool
allProps xs = prop_lengthPreserved xs &&
              prop_isSorted xs &&
              prop_isPermutation xs

main : IO ()
main = do
  putStrLn "=== Running Property Tests for List Sorting ==="
  putStrLn "Testing 1000 randomly generated lists..."
  
  -- Run property tests
  printVerdict
    (genNatList (limit 100))     -- Generator with fuel for list size
    (coverWith 100.percent allProps)  -- Property to test
    (limit 1000)                 -- Number of test cases
  
  putStrLn "=== Tests Complete ==="
```

**What to do**: Add this `main` function to complete your file.

**Expected result**: You now have a complete property testing program.

## Step 6: Compile and run your tests

Let's see property-based testing in action!

First, compile your program:
```bash
idris2 SortingTest.idr -o sortingtest
```

Then run it:
```bash
./sortingtest
```

**What you should see**: Output similar to this:
```
=== Running Property Tests for List Sorting ===
Testing 1000 randomly generated lists...
✓ Property holds for 1000 tests.
Coverage of List: 100.00%
  - Nil: 12.30%
  - (::): 87.70%
Coverage of Nat: 100.00%
=== Tests Complete ===
```

**What this shows you**: DepTyCheck successfully tested 1000 different lists and verified that all three properties held for every single one!

**Notice the coverage information**: This shows what percentage of tests involved empty lists vs. non-empty lists, giving you confidence that edge cases were tested.

## Step 7: Experiment with broken code

Let's see what happens when our sorting function has a bug. Try modifying the `sortNatList` function:

```idris
-- Change this line:
sortNatList : List Nat -> List Nat
sortNatList = sort

-- To this broken version:
sortNatList : List Nat -> List Nat
sortNatList = reverse . sort  -- This reverses after sorting!
```

**What to do**: Replace the working sort function with this broken version.

**Expected result**: When you recompile and run, you should see test failures.

**What you'll learn**: Property-based testing catches bugs that might be missed by manual testing. The `prop_isSorted` property will fail because the reversed list won't be in order.

## What we accomplished

Congratulations! You've successfully created and run your first property-based test suite.

**Key achievements**:
- ✅ Defined a function to test (list sorting)
- ✅ Created automatic test data generation
- ✅ Expressed software properties as boolean functions
- ✅ Ran automated property verification
- ✅ Understood test results and coverage information

**Key concepts you've learned**:
- How to think about software correctness in terms of properties
- The difference between example-based testing and property-based testing
- How DepTyCheck automatically generates diverse test cases
- How to interpret test results and coverage reports

## Next steps

Ready to learn more? Try these:

- **Tutorial 3**: Controlling Recursion in Generated Data - Learn how Fuel works with recursive types
- **Tutorial 4**: Customizing Generators with Basic Combinators - Gain more control over generated data
- **Experiment**: Try testing other functions like list reversal, filtering, or your own custom functions

Remember: Property-based testing is most powerful when testing functions with clear mathematical properties. The clearer your properties, the more effective your tests will be!

---

*This tutorial follows Diataxis principles by providing concrete, actionable steps with immediate feedback and learning reinforcement.*

### What we accomplished
Congratulations! You've successfully written and executed your first full property-based test suite using `DepTyCheck`.

You have learned to:
- **Define a function to be tested** (`sortNatList`).
- **Derive an input generator** for that function (`genNatList`).
- **Express fundamental characteristics of correct behavior as testable properties** (`prop_lengthPreserved`, `prop_isSorted`, `prop_isPermutation`, `allProps`).
- **Execute property tests** using `printVerdict` and analyze the test report.

This workflow is central to property-based testing and forms the foundation for building highly robust and reliable software in Idris 2.

### Next steps
To further enhance your `DepTyCheck` skills, consider these tutorials:
- **Controlling Recursion in Generated Data (e.g., for Trees)**: Deepen your understanding of `Fuel` for complex and recursive types.
- **Customizing Generators with Basic Combinators**: Learn how to gain more granular control over your generated data when `deriveGen` is not enough.

Or, experiment further:
- Implement `prop_isPermutation` more rigorously (e.g., by checking if `count x xs == count x (sortNatList xs)` for all elements `x`).
- Write properties for other functions you've implemented or found in the Idris standard library.