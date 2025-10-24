# Mastering Dependent Data: Generating Sorted Lists

## What We'll Accomplish
In this tutorial, we'll learn how to generate data for dependent types that enforce sorting invariants. By the end, you'll:
- Create a dependently typed sorted list
- Use `deriveGen` to generate type-correct sorted lists
- Understand how DepTyCheck handles complex type constraints
- Have a working example demonstrating dependent type generation

## Prerequisites
Before we begin, make sure you have:
- Completed the "Generate Test Data for a Simple Type with `deriveGen`" tutorial
- Basic understanding of dependent types in Idris
- Idris 2 installed and DepTyCheck available in your project

## Step 1: Create a Simple Sorted List

Let's start with a basic sorted list that maintains ordering. Create a new file called `SortedListLearning.idr`:

```idris
module SortedListLearning

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.Nat

%language ElabReflection

data SortedNatList : Nat -> Type where
  SNil : SortedNatList 0
  SCons : (x : Nat) -> (xs : SortedNatList x) -> SortedNatList x

genSortedNatList : (maxVal : Nat) -> Fuel -> Gen MaybeEmpty (SortedNatList maxVal)
genSortedNatList maxVal fuel = deriveGen

main : IO ()
main = do
  putStrLn "Generating sorted lists:"
  let smallLists = take 3 $ unGen1 (limit 5) (genSortedNatList 3 (limit 5))
  let mediumLists = take 3 $ unGen1 (limit 5) (genSortedNatList 10 (limit 5))
  
  putStrLn "Small lists (max 3):"
  traverse_ (putStrLn . show) smallLists
  
  putStrLn "\nMedium lists (max 10):"
  traverse_ (putStrLn . show) mediumLists
```

**Expected result**: You should see lists where each element is less than or equal to the previous element.

**What to notice**: The type system ensures the sorting invariant is maintained.

## Step 2: Create a More Flexible Sorted List

Now let's create a sorted list that can handle any ordering:

```idris
-- Add to your existing file
data Ordering = LT | EQ | GT

data SortedList : (a : Type) -> (compare : a -> a -> Ordering) -> Type where
  Empty : SortedList a compare
  Single : (x : a) -> SortedList a compare
  Cons : (x : a) -> (xs : SortedList a compare) -> 
          {auto prf : compare x (head xs) /= LT} -> SortedList a compare

head : SortedList a compare -> Maybe a
head Empty = Nothing
head (Single x) = Just x
head (Cons x xs) = Just x

natCompare : Nat -> Nat -> Ordering
natCompare Z Z = EQ
natCompare Z (S _) = LT
natCompare (S _) Z = GT
natCompare (S m) (S n) = natCompare m n

genSortedList : Fuel -> Gen MaybeEmpty (SortedList Nat natCompare)
genSortedList fuel = deriveGen

testSortedList : IO ()
testSortedList = do
  putStrLn "Generating sorted lists with custom ordering:"
  let results = take 5 $ unGen1 (limit 5) genSortedList
  traverse_ (putStrLn . show) results

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testSortedList
```

**Expected result**: You should see lists that are sorted according to the custom comparison function.

**What to notice**: DepTyCheck handles the proof obligation automatically.

## Step 3: Handle Complex Sorting Constraints

Let's create a sorted list with more complex constraints:

```idris
-- Add to your existing file
data StrictlySorted : Nat -> Type where
  StrictNil : StrictlySorted 0
  StrictCons : (x : Nat) -> 
               (xs : StrictlySorted x) -> 
               {auto prf : x > headVal xs} -> StrictlySorted x

headVal : StrictlySorted n -> Nat
headVal StrictNil = 0
headVal (StrictCons x xs) = x

genStrictlySorted : (maxVal : Nat) -> Fuel -> Gen MaybeEmpty (StrictlySorted maxVal)
genStrictlySorted maxVal fuel = deriveGen

testStrictlySorted : IO ()
testStrictlySorted = do
  putStrLn "Generating strictly sorted lists:"
  let results = take 3 $ unGen1 (limit 5) (genStrictlySorted 10 (limit 5))
  traverse_ (putStrLn . show) results

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testStrictlySorted
```

**Expected result**: You should see lists where each element is strictly greater than the previous.

**What to notice**: The strict inequality constraint is automatically satisfied.

## Step 4: Create a Balanced Sorted Tree

Let's extend our sorting concept to trees:

```idris
-- Add to your existing file
data SortedTree : Nat -> Nat -> Type where
  Leaf : SortedTree min max
  Node : (value : Nat) -> 
         (left : SortedTree min value) -> 
         (right : SortedTree value max) -> 
         SortedTree min max

genSortedTree : (minVal : Nat) -> (maxVal : Nat) -> Fuel -> Gen MaybeEmpty (SortedTree minVal maxVal)
genSortedTree minVal maxVal fuel = deriveGen

testSortedTree : IO ()
testSortedTree = do
  putStrLn "Generating sorted trees:"
  let results = take 3 $ unGen1 (limit 5) (genSortedTree 0 10 (limit 5))
  traverse_ (putStrLn . show) results

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testSortedTree
```

**Expected result**: You should see binary search trees where all values are properly ordered.

**What to notice**: DepTyCheck handles the complex ordering constraints in tree structures.

## What We Accomplished

Congratulations! We've successfully learned how to generate data for complex dependent types:
- Created sorted lists with various ordering constraints
- Extended sorting concepts to tree structures
- Used `deriveGen` to automatically generate type-correct data

You now have the skills to generate test data for sophisticated dependent types that maintain complex invariants.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Generating Unique Lists and Vectors
- How-to: Testing Sorting Algorithms with Generated Data
- Explanation: How DepTyCheck Resolves Complex Constraints

Or experiment by creating your own dependent types with custom invariants and see how DepTyCheck handles them.