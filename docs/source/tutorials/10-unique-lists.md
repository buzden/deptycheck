# Mastering Complex Constraints: Generating Unique Lists

## What We'll Accomplish
In this tutorial, we'll learn how to generate data types that enforce uniqueness constraints. By the end, you'll:
- Create dependent types that guarantee element uniqueness
- Use `deriveGen` to generate valid unique lists
- Understand how DepTyCheck handles complex constraints
- Have a working example demonstrating unique list generation

## Prerequisites
Before we begin, make sure you have:
- Completed the "Generate Test Data for a Simple Type with `deriveGen`" tutorial
- Basic understanding of dependent types in Idris
- Idris 2 installed and DepTyCheck available in your project

## Step 1: Create a Simple Unique List

Let's start by creating a type that ensures all elements are unique. Create a new file called `UniqueLearning.idr`:

```idris
module UniqueLearning

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.List
import Data.Nat

%language ElabReflection

data UniqueNatList : Type where
  UNil : UniqueNatList
  UCons : (x : Nat) -> (xs : UniqueNatList) -> 
          {auto prf : Not (elem x (toList xs))} -> UniqueNatList

where
  toList : UniqueNatList -> List Nat
  toList UNil = []
  toList (UCons x xs prf) = x :: toList xs

genUniqueNatList : Fuel -> Gen MaybeEmpty UniqueNatList
genUniqueNatList fuel = deriveGen

main : IO ()
main = do
  putStrLn "Generating unique lists:"
  let results = take 5 $ unGen1 (limit 10) genUniqueNatList
  traverse_ (putStrLn . show) results
```

**Expected result**: You should see lists where all elements are unique.

**What to notice**: The `Not (elem x (toList xs))` constraint ensures no duplicates.

## Step 2: Create a More Structured Unique List

Now let's create a unique list with better structure:

```idris
-- Add to your existing file
data UniqList : (maxSize : Nat) -> Type where
  UniqNil : UniqList 0
  UniqCons : (x : Nat) -> 
             (xs : UniqList n) -> 
             {auto prf : Not (elem x (toUniqList xs))} -> 
             UniqList (S n)

where
  toUniqList : UniqList n -> List Nat
  toUniqList UniqNil = []
  toUniqList (UniqCons x xs prf) = x :: toUniqList xs

genUniqList : (maxSize : Nat) -> Fuel -> Gen MaybeEmpty (UniqList maxSize)
genUniqList maxSize fuel = deriveGen

testUniqList : IO ()
testUniqList = do
  putStrLn "Generating unique lists with size constraints:"
  let smallLists = take 3 $ unGen1 (limit 5) (genUniqList 3 (limit 5))
  let largeLists = take 3 $ unGen1 (limit 5) (genUniqList 5 (limit 5))
  
  putStrLn "Small unique lists (max 3 elements):"
  traverse_ (putStrLn . show) smallLists
  
  putStrLn "\nLarge unique lists (max 5 elements):"
  traverse_ (putStrLn . show) largeLists

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testUniqList
```

**Expected result**: You should see uniquely-sized lists with no duplicate elements.

**What to notice**: The size parameter helps control the complexity of generation.

## Step 3: Create a Unique Vector

Let's extend our uniqueness concept to vectors:

```idris
-- Add to your existing file
import Data.Vect

data UniqueVect : (len : Nat) -> (upperBound : Nat) -> Type where
  UVNil : UniqueVect 0 n
  UVCons : (x : Fin (S n)) -> 
           (xs : UniqueVect k n) -> 
           {auto prf : Not (elem x (toVect xs))} -> 
           UniqueVect (S k) n

where
  toVect : UniqueVect len n -> Vect len (Fin (S n))
  toVect UVNil = []
  toVect (UVCons x xs prf) = x :: toVect xs

genUniqueVect : (len : Nat) -> (upperBound : Nat) -> Fuel -> Gen MaybeEmpty (UniqueVect len upperBound)
genUniqueVect len upperBound fuel = deriveGen

testUniqueVect : IO ()
testUniqueVect = do
  putStrLn "Generating unique vectors:"
  let smallVects = take 3 $ unGen1 (limit 5) (genUniqueVect 3 10 (limit 5))
  let largeVects = take 3 $ unGen1 (limit 5) (genUniqueVect 5 20 (limit 5))
  
  putStrLn "Small unique vectors:"
  traverse_ (putStrLn . show) smallVects
  
  putStrLn "\nLarge unique vectors:"
  traverse_ (putStrLn . show) largeVects

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testUniqueVect
```

**Expected result**: You should see vectors with unique elements from a bounded range.

**What to notice**: The Fin type helps control the element domain.

## Step 4: Handle Complex Uniqueness Constraints

Let's create a type with multiple uniqueness constraints:

```idris
-- Add to your existing file
data PairUniq : Type where
  MkPairUniq : (x : Nat) -> (y : Nat) -> 
               {auto prf1 : x /= y} -> 
               {auto prf2 : x + y < 20} -> 
               PairUniq

genPairUniq : Fuel -> Gen MaybeEmpty PairUniq
genPairUniq fuel = deriveGen

testPairUniq : IO ()
testPairUniq = do
  putStrLn "Generating unique pairs:"
  let results = take 5 $ unGen1 (limit 10) genPairUniq
  traverse_ (putStrLn . show) results

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testPairUniq
```

**Expected result**: You should see pairs where x ≠ y and their sum is less than 20.

**What to notice**: DepTyCheck handles multiple simultaneous constraints.

## What We Accomplished

Congratulations! We've successfully learned how to generate data with uniqueness constraints:
- Created various types that enforce element uniqueness
- Extended uniqueness to vectors and structured types
- Handled multiple simultaneous constraints
- Used `deriveGen` to automatically generate valid data

You now have the skills to generate test data for types with complex uniqueness requirements.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Generating ASTs for Domain-Specific Languages
- How-to: Testing Functions That Require Unique Inputs
- Explanation: How DepTyCheck Solves Complex Constraints

Or experiment by creating your own types with custom uniqueness constraints and see how DepTyCheck handles them.