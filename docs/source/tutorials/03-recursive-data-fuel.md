# Controlling Recursion in Generated Data (e.g., for Trees)

## Introduction

In this tutorial, we'll explore how DepTyCheck handles recursive data types using the `Fuel` mechanism. You'll learn how to generate binary trees of varying complexity and understand how `Fuel` prevents infinite recursion during generation.

By the end of this tutorial, you will have:
- A working generator for recursive binary trees
- Understanding of how `Fuel` controls generation depth
- Practical experience observing Fuel's impact on generated data
- Knowledge of recursion management in property-based testing

### What we'll build together
We'll create a binary tree data type and use `deriveGen` to automatically generate trees. You'll see firsthand how changing the `Fuel` parameter affects the size and complexity of the generated trees.

**Expected learning time**: 20-25 minutes

## Prerequisites

Before we begin, make sure you have:

- Completed Tutorial 1: "Generating Test Data for a Simple Type with `deriveGen`"
- Idris 2 and DepTyCheck installed and working
- Basic understanding of recursive data structures

## Step 1: Create the file and define a binary tree

Let's start by creating our recursive data structure - a simple binary tree.

Create a new file called `TreeFuel.idr` and add this code:

```idris
module TreeFuel

%language ElabReflection

import Data.Nat
import Data.Fuel
import Test.DepTyCheck.Gen

-- A recursive binary tree data type
data BinTree : Type where
  Leaf : Nat -> BinTree                    -- Leaf node with a value
  Node : BinTree -> Nat -> BinTree -> BinTree  -- Internal node with left/right subtrees
```

**What to do**: Create the file and add this tree definition.

**Expected result**: You have a recursive binary tree type ready for generation.

**What you'll notice**: The `Node` constructor is recursive - it contains two `BinTree` values. This is what makes `Fuel` necessary.

### Prerequisites
Before diving into recursive data generation, please ensure you have:
- **Completed \"Generate Test Data for a Simple Type with `deriveGen`\"**: This tutorial leverages basic `deriveGen` usage.
- Idris 2 installed and `DepTyCheck` set up in your project.
- Basic familiarity with defining recursive data types in Idris.

### Step 1: Define a Recursive Binary Tree Data Type
Our subject for today is a simple binary tree. This structure is inherently recursive, as each internal node contains more trees. For illustration, our tree will store natural numbers in both its leaves and internal nodes.

Create a new file named `BinaryTree.idr` in your project directory and add the following code:

```idris
module BinaryTree

import Data.Nat -- For natural numbers, the payload of our tree

-- Our recursive binary tree data type
data BinTree : Type where
  Leaf : Nat -> BinTree                            -- A leaf node contains a single natural number
  Node : BinTree -> Nat -> BinTree -> BinTree -- An internal node contains two sub-trees and a natural number
```

**Expected result**: Saving the file should compile without errors. You have now defined the blueprint for a simple binary tree.

**What to notice**: 
- `Leaf` is our base case for the recursion; it simply holds a `Nat`.
- `Node` is our recursive case. It takes two `BinTree` arguments (for the left and right sub-trees) and a `Nat` (for the value at this node). This self-referential definition is what makes `BinTree` a recursive type. If `DepTyCheck` were to blindly generate `Node` constructors, it would recurse infinitely without a mechanism to stop it.

## Step 2: Derive a generator for the recursive tree

Now let's use `deriveGen` to automatically create a generator for our binary tree. DepTyCheck will handle the recursion automatically.

Add the generator definition to your file:

```idris
module TreeFuel

%language ElabReflection

import Data.Nat
import Data.Fuel
import Test.DepTyCheck.Gen

data BinTree : Type where
  Leaf : Nat -> BinTree
  Node : BinTree -> Nat -> BinTree -> BinTree

-- Automatically derive a generator for BinTree
genBinTree : Fuel -> Gen MaybeEmpty BinTree
genBinTree = deriveGen
```

**What to do**: Add the `genBinTree` function definition.

**Expected result**: Your file should compile without errors.

**What you'll notice**: The generator signature `Fuel -> Gen MaybeEmpty BinTree` looks familiar, but now the `Fuel` parameter is crucial because `BinTree` is recursive.

**Try compiling**: Check that everything works:
```bash
idris2 --check TreeFuel.idr
```

You should see no compilation errors.

## Step 3: Create a helper to run the generator

We need a way to run our tree generator with different Fuel values so we can observe the effects.

Add this helper function to your file:

```idris
module TreeFuel

%language ElabReflection

import Data.Nat
import Data.Fuel
import Test.DepTyCheck.Gen
import Control.Monad.RWS
import Control.Monad.Random

data BinTree : Type where
  Leaf : Nat -> BinTree
  Node : BinTree -> Nat -> BinTree -> BinTree

genBinTree : Fuel -> Gen MaybeEmpty BinTree
genBinTree = deriveGen

-- Helper to run generator with specific Fuel
runTreeGen : Fuel -> IO BinTree
runTreeGen fuel = do
  seed <- getRandomSeed
  let (value, _) = runRandom seed (runGen fuel (genBinTree fuel))
  case value of
    Nothing => fail "Generator failed!"
    Just v  => pure v
```

**What to do**: Add the `runTreeGen` helper function.

**Expected result**: You now have a way to generate individual trees.

## Step 4: Create the main function to demonstrate Fuel effects

Now let's create a program that shows how different Fuel values affect tree generation.

Add the main function:

```idris
module TreeFuel

%language ElabReflection

import Data.Nat
import Data.Fuel
import Test.DepTyCheck.Gen
import Control.Monad.RWS
import Control.Monad.Random

data BinTree : Type where
  Leaf : Nat -> BinTree
  Node : BinTree -> Nat -> BinTree -> BinTree

genBinTree : Fuel -> Gen MaybeEmpty BinTree
genBinTree = deriveGen

runTreeGen : Fuel -> IO BinTree
runTreeGen fuel = do
  seed <- getRandomSeed
  let (value, _) = runRandom seed (runGen fuel (genBinTree fuel))
  case value of
    Nothing => fail "Generator failed!"
    Just v  => pure v

main : IO ()
main = do
  putStrLn "=== Observing Fuel Effects on Tree Generation ==="
  
  putStrLn "\n1. Very low Fuel (limit 1) - mostly leaves:"
  tree1 <- runTreeGen (limit 1)
  putStrLn $ "Tree: " ++ show tree1
  
  putStrLn "\n2. Medium Fuel (limit 3) - some nesting:"
  tree2 <- runTreeGen (limit 3)
  putStrLn $ "Tree: " ++ show tree2
  
  putStrLn "\n3. High Fuel (limit 10) - complex trees:"
  tree3 <- runTreeGen (limit 10)
  putStrLn $ "Tree: " ++ show tree3
  
  putStrLn "\n4. Another high Fuel example:"
  tree4 <- runTreeGen (limit 10)
  putStrLn $ "Tree: " ++ show tree4
  
  putStrLn "\n=== Experiment Complete ==="
```

**What to do**: Add this complete main function.

**Expected result**: You now have a complete program that demonstrates Fuel's impact.

## Step 5: Compile and run the demonstration

Let's see Fuel in action!

First, compile your program:
```bash
idris2 TreeFuel.idr -o treefuel
```

Then run it:
```bash
./treefuel
```

**What you should see**: Output similar to this (exact trees will vary):
```
=== Observing Fuel Effects on Tree Generation ===

1. Very low Fuel (limit 1) - mostly leaves:
Tree: Leaf 5

2. Medium Fuel (limit 3) - some nesting:
Tree: Node (Leaf 2) 7 (Leaf 3)

3. High Fuel (limit 10) - complex trees:
Tree: Node (Node (Leaf 1) 4 (Leaf 2)) 8 (Node (Leaf 0) 6 (Leaf 3))

4. Another high Fuel example:
Tree: Node (Leaf 9) 5 (Node (Node (Leaf 1) 2 (Leaf 0)) 7 (Leaf 4))

=== Experiment Complete ===
```

**What this shows you**: Higher Fuel values allow for deeper, more complex tree structures. With low Fuel, you mostly get simple leaves.

## Step 6: Experiment with different Fuel values

Try modifying the Fuel values in your `main` function:

- Change `limit 1` to `limit 0` - see what happens with no Fuel
- Try `limit 20` for very complex trees
- Add more examples with intermediate values like `limit 5`

**What you'll learn**: Fuel controls the "depth budget" for recursive generation. Each recursive call consumes Fuel, and when it runs out, DepTyCheck favors non-recursive constructors.

## What we accomplished

Congratulations! You've successfully explored how DepTyCheck handles recursive data generation.

**Key achievements**:
- ✅ Defined a recursive binary tree data type
- ✅ Used `deriveGen` to create a recursive generator
- ✅ Observed how Fuel controls generation complexity
- ✅ Understood recursion management in property-based testing

**Key concepts you've learned**:
- How recursive data types require Fuel for termination
- The relationship between Fuel values and generation depth
- How DepTyCheck automatically manages recursion
- Why Fuel is essential for generating finite test data

## Next steps

Ready to learn more? Try these:

- **Tutorial 4**: Customizing Generators with Basic Combinators - Learn to fine-tune generation
- **Tutorial 5**: Understanding Generator Emptiness - Explore type-level guarantees
- **Experiment**: Create other recursive types like linked lists or expression trees

Remember: Fuel is your friend when working with recursive types - it ensures your generators always terminate while still producing interesting test cases!

---

*This tutorial follows Diataxis principles by providing hands-on experimentation with immediate visual feedback.*

### What we accomplished
Congratulations! You've successfully investigated the crucial role of `Fuel` in generating recursive data structures with `DepTyCheck`.

Here’s a recap of what you’ve learned:
- **Defined a recursive `BinTree` data type**: A classic example of a structure requiring careful recursion handling.
- **Used `deriveGen` for recursive types**: Demonstrated that `deriveGen` automatically manages the complexity of generating recursive data.
- **Observed the impact of `Fuel`**: You visually confirmed how the `Fuel` parameter directly controls the size and complexity of generated recursive values.
- **Gained insight into `DepTyCheck`'s internal mechanisms**: You now have a better understanding of how `Fuel` is used to prevent infinite recursion during data generation.

This knowledge is vital for effectively testing programs that operate on recursive data, as it allows you to control the size and complexity of your test inputs.

### Next steps
To further enhance your `DepTyCheck` skills, consider these tutorials:
- **Customizing Generators with Basic Combinators**: Combine `deriveGen` with other combinators for even more control.
- **Generating Dependent Data with GADT Constructors**: Tackle more complex dependent types that use recursion and type-level proofs.

Or, feel free to experiment with what you've learned:
- Modify the `BinTree` data type (e.g., add a new constructor, change the payload type) and re-run the generator to see how `DepTyCheck` still manages recursion.
- Try defining a list generator manually and observe the challenges of building in termination logic without `Fuel` (or reimplementing a basic `Fuel`-like system).