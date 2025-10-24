# Mastering Custom Generators: Building Hand-Written Generators

## What We'll Accomplish
In this tutorial, we'll learn how to create sophisticated custom generators from scratch. By the end, you'll:
- Build generators for complex data structures
- Control value distributions precisely
- Combine multiple generation strategies
- Have comprehensive generator-building skills

## Prerequisites
Before we begin, make sure you have:
- Completed the "Test your first function" tutorial
- Basic understanding of monads in Idris
- DepTyCheck library installed

## Step 1: Create Simple Custom Generators

Let's start by building basic generators manually. Create `CustomGeneratorLearning.idr`:

```idris
module CustomGeneratorLearning

import Data.Fuel
import Test.DepTyCheck.Gen

%default total

-- Basic element generator
genSmallNats : Gen NonEmpty Nat
genSmallNats = elements [0, 1, 2, 3, 4, 5]

-- Generator with mapping
genEvenNats : Gen NonEmpty Nat
genEvenNats = map (\n => n * 2) genSmallNats

-- Generator composition
genNameNumberPair : Gen NonEmpty (String, Nat)
genNameNumberPair = do
  name <- elements ["Alice", "Bob", "Charlie"]
  num <- genSmallNats
  pure (name, num)

main : IO ()
main = do
  putStrLn "Testing basic generators:"
  let nats = take 5 $ unGen1 (limit 10) genSmallNats
  let evens = take 5 $ unGen1 (limit 10) genEvenNats
  let pairs = take 5 $ unGen1 (limit 10) genNameNumberPair
  
  putStrLn "Small nats:"
  traverse_ (putStrLn . show) nats
  
  putStrLn "\nEven nats:"
  traverse_ (putStrLn . show) evens
  
  putStrLn "\nName-number pairs:"
  traverse_ (putStrLn . show) pairs
```

**Expected result**: You should see various generated values.

**What to notice**: Monadic composition allows flexible generator building.

## Step 2: Control Generator Distributions

Let's explore probability control in custom generators:

```idris
-- Continue in CustomGeneratorLearning.idr

-- Uniform distribution
genUniformColors : Gen NonEmpty String
genUniformColors = elements ["red", "green", "blue", "yellow"]

-- Weighted distribution
genWeightedColors : Gen NonEmpty String
genWeightedColors = frequency
  [ (3, pure "red")    -- 30% probability
  , (2, pure "green")  -- 20% probability
  , (4, pure "blue")   -- 40% probability  
  , (1, pure "yellow") -- 10% probability
  ]

-- Conditional generation
genValidAge : Gen NonEmpty Nat
genValidAge = suchThat (elements [0..150]) (\age => age >= 18 && age <= 120)

testDistributions : IO ()
testDistributions = do
  putStrLn "Testing distribution control:"
  
  putStrLn "Uniform colors:"
  let uniformColors = take 10 $ unGen1 (limit 10) genUniformColors
  traverse_ (putStrLn . show) uniformColors
  
  putStrLn "\nWeighted colors:"
  let weightedColors = take 10 $ unGen1 (limit 10) genWeightedColors
  traverse_ (putStrLn . show) weightedColors
  
  putStrLn "\nValid ages:"
  let validAges = take 5 $ unGen1 (limit 10) genValidAge
  traverse_ (putStrLn . show) validAges

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testDistributions
```

**Expected result**: You should see different distributions and constrained values.

**What to notice**: `suchThat` adds constraints to existing generators.

## Step 3: Build Recursive Generators

Now let's create generators for recursive data structures:

```idris
-- Continue in CustomGeneratorLearning.idr

data Tree a = Leaf a | Node (Tree a) (Tree a)

-- Manual recursive generator
genTree : Fuel -> Gen MaybeEmpty (Tree Nat)
genTree Dry = Leaf <$> elements [0, 1, 2]
genTree (More fuel) = oneOf
  [ Leaf <$> elements [0, 1, 2, 3, 4, 5]
  , do
      left <- genTree fuel
      right <- genTree fuel
      pure (Node left right)
  ]

-- List generator with size control
genBoundedList : Nat -> Gen MaybeEmpty (List Nat)
genBoundedList Z = pure []
genBoundedList (S n) = oneOf
  [ pure []
  , do
      x <- elements [0..10]
      xs <- genBoundedList n
      pure (x :: xs)
  ]

testRecursive : IO ()
testRecursive = do
  putStrLn "Testing recursive generators:"
  
  putStrLn "Small trees:"
  let smallTrees = take 3 $ unGen1 (limit 3) (genTree (limit 3))
  traverse_ (putStrLn . show) smallTrees
  
  putStrLn "\nBounded lists:"
  let boundedLists = take 3 $ unGen1 (limit 5) (genBoundedList 5)
  traverse_ (putStrLn . show) boundedLists

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testRecursive
```

**Expected result**: You should see tree and list structures with controlled sizes.

**What to notice**: Fuel and size parameters prevent infinite recursion.

## Step 4: Advanced Generator Patterns

Let's create more sophisticated generators:

```idris
-- Continue in CustomGeneratorLearning.idr

-- Generator with state tracking
genIncreasingPairs : Gen NonEmpty (Nat, Nat)
genIncreasingPairs = do
  first <- elements [0..100]
  second <- elements [first..100]
  pure (first, second)

-- Complex conditional generator
genValidTriangle : Gen MaybeEmpty (Nat, Nat, Nat)
genValidTriangle = suchThat genTriple isValidTriangle
where
  genTriple : Gen NonEmpty (Nat, Nat, Nat)
  genTriple = do
    a <- elements [1..20]
    b <- elements [1..20]
    c <- elements [1..20]
    pure (a, b, c)
    
  isValidTriangle : (Nat, Nat, Nat) -> Bool
  isValidTriangle (a, b, c) = a + b > c && a + c > b && b + c > a

testAdvanced : IO ()
testAdvanced = do
  putStrLn "Testing advanced patterns:"
  
  putStrLn "Increasing pairs:"
  let pairs = take 5 $ unGen1 (limit 10) genIncreasingPairs
  traverse_ (putStrLn . show) pairs
  
  putStrLn "\nValid triangles:"
  let triangles = take 5 $ unGen1 (limit 10) genValidTriangle
  traverse_ (putStrLn . show) triangles

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testAdvanced
```

**Expected result**: You should see valid mathematical structures.

**What to notice**: Complex constraints can be applied to generators.

## What We Accomplished

Congratulations! We've mastered custom generator creation:
- Built generators with various distribution patterns
- Created recursive generators with size control
- Implemented complex constraints and conditions
- Combined multiple generation strategies

You now have the skills to build sophisticated custom generators for any data structure.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Integrating Custom Generators with Automatic Derivation
- How-to: Optimizing Generator Performance
- Explanation: Advanced Generator Composition Patterns

Or experiment by creating generators for your specific domain models with complex business rules.