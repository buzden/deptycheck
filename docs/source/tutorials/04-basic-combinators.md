# Customizing Generators with Basic Combinators

## Introduction

In this tutorial, you'll learn how to customize and combine generators using DepTyCheck's combinator functions. While `deriveGen` is powerful for automatic generation, combinators give you precise control over what data gets generated.

By the end of this tutorial, you will have:
- Experience using `oneOf` for explicit choices
- Understanding of `map` for value transformation
- Knowledge of `suchThat` for filtering
- Practical skills in generator composition

### What we'll build together
We'll create generators that:
- Choose from specific values using `oneOf`
- Transform generated data using `map`
- Filter results using `suchThat` predicates

**Expected learning time**: 25-30 minutes

## Prerequisites

Before we begin, make sure you have:

- Completed Tutorial 1: "Generating Test Data for a Simple Type with `deriveGen`"
- Idris 2 and DepTyCheck installed and working
- Basic familiarity with functional programming concepts

## Step 1: Create the file and set up imports

Let's start by creating our combinator experiment file.

Create a new file called `Combinators.idr` and add this code:

```idris
module Combinators

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.Nat
```

**What to do**: Create the file and add these imports.

**Expected result**: You have a basic file ready for combinator experiments.

### Prerequisites
To get the most out of this tutorial, please ensure you have:
- **Completed \"Generate Test Data for a Simple Type with `deriveGen`\"**: This tutorial builds upon the foundation of `deriveGen`.
- **Completed \"Controlling Recursion in Generated Data (e.g., for Trees)\"**: A good understanding of `Fuel` is beneficial, as generators often require it.
- Idris 2 installed and `DepTyCheck` set up in your project.
- Basic familiarity with Idris's type classes like `Functor` and monadic style programming (`do` notation, `>>=`).

## Step 2: Create a helper function and try `oneOf`

Let's create a helper function to run generators and then experiment with `oneOf`.

Add this code to your file:

```idris
module Combinators

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.Nat
import Control.Monad.RWS
import Control.Monad.Random

-- Helper to run any generator and print result
runGenAndShow : {em : Emptiness} -> {a : Type} -> Fuel -> Gen em a -> IO ()
runGenAndShow fuel gen = do
  seed <- getRandomSeed
  let (value, _) = runRandom seed (runGen fuel gen)
  case value of
    Nothing => putStrLn "✗ Generator failed"
    Just v  => putStrLn $ "✓ " ++ show v
```

**What to do**: Add the helper function.

**Expected result**: You now have a reusable way to test generators.

## Step 3: Experiment with `oneOf` for explicit choices

`oneOf` lets you choose randomly from a set of alternatives. Let's create a color generator.

Add this section:

```idris
module Combinators

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.Nat
import Control.Monad.RWS
import Control.Monad.Random

runGenAndShow : {em : Emptiness} -> {a : Type} -> Fuel -> Gen em a -> IO ()
runGenAndShow fuel gen = do
  seed <- getRandomSeed
  let (value, _) = runRandom seed (runGen fuel gen)
  case value of
    Nothing => putStrLn "✗ Generator failed"
    Just v  => putStrLn $ "✓ " ++ show v

-- Using oneOf to choose from specific values
genColor : Gen MaybeEmpty String
genColor = oneOf (altsFromList [pure "Red", pure "Green", pure "Blue"])

main : IO ()
main = do
  putStrLn "=== Testing oneOf Combinator ==="
  putStrLn "Generating 5 colors from {Red, Green, Blue}:"
  
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  
  putStrLn "=== oneOf Test Complete ==="
```

**What to do**: Add the `genColor` generator and main function.

**What you'll notice**: `oneOf` takes alternatives created with `pure` and randomly chooses between them.

**Try compiling**: Check everything works:
```bash
idris2 --check Combinators.idr
```

## Step 4: Try `map` for transforming values

`map` lets you transform generated values. Let's create a generator that produces string versions of natural numbers.

Update your file with the map example:

```idris
module Combinators

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.Nat
import Control.Monad.RWS
import Control.Monad.Random

runGenAndShow : {em : Emptiness} -> {a : Type} -> Fuel -> Gen em a -> IO ()
runGenAndShow fuel gen = do
  seed <- getRandomSeed
  let (value, _) = runRandom seed (runGen fuel gen)
  case value of
    Nothing => putStrLn "✗ Generator failed"
    Just v  => putStrLn $ "✓ " ++ show v

-- oneOf example
genColor : Gen MaybeEmpty String
genColor = oneOf (altsFromList [pure "Red", pure "Green", pure "Blue"])

-- map example: transform Nat generator to String generator
genNat : Fuel -> Gen MaybeEmpty Nat
genNat = deriveGen

genNatString : Fuel -> Gen MaybeEmpty String
genNatString fuel = map show (genNat fuel)

main : IO ()
main = do
  putStrLn "=== Testing oneOf Combinator ==="
  putStrLn "Generating 5 colors from {Red, Green, Blue}:"
  
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  
  putStrLn "\n=== Testing map Combinator ==="
  putStrLn "Generating 3 natural numbers as strings:"
  
  runGenAndShow (limit 10) (genNatString (limit 10))
  runGenAndShow (limit 10) (genNatString (limit 10))
  runGenAndShow (limit 10) (genNatString (limit 10))
  
  putStrLn "=== Combinator Tests Complete ==="
```

**What to do**: Add the map-based generator and update the main function.

**What you'll notice**: `map` applies a function (`show`) to values from another generator (`genNat`), creating a new generator.

**Expected output**: You'll see both colors and stringified numbers.

## Step 5: Try `suchThat` for filtering results

`suchThat` filters generated values using a predicate. Let's create a generator for even numbers only.

Complete your file with the suchThat example:

```idris
module Combinators

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.Nat
import Control.Monad.RWS
import Control.Monad.Random

runGenAndShow : {em : Emptiness} -> {a : Type} -> Fuel -> Gen em a -> IO ()
runGenAndShow fuel gen = do
  seed <- getRandomSeed
  let (value, _) = runRandom seed (runGen fuel gen)
  case value of
    Nothing => putStrLn "✗ Generator failed"
    Just v  => putStrLn $ "✓ " ++ show v

-- oneOf example
genColor : Gen MaybeEmpty String
genColor = oneOf (altsFromList [pure "Red", pure "Green", pure "Blue"])

-- map example
genNat : Fuel -> Gen MaybeEmpty Nat
genNat = deriveGen

genNatString : Fuel -> Gen MaybeEmpty String
genNatString fuel = map show (genNat fuel)

-- suchThat example: only even numbers
genEvenNat : Fuel -> Gen MaybeEmpty Nat
genEvenNat fuel = suchThat (genNat fuel) (\n => n `mod` 2 == 0)

main : IO ()
main = do
  putStrLn "=== Testing oneOf Combinator ==="
  putStrLn "Generating 5 colors from {Red, Green, Blue}:"
  
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  runGenAndShow (limit 10) genColor
  
  putStrLn "\n=== Testing map Combinator ==="
  putStrLn "Generating 3 natural numbers as strings:"
  
  runGenAndShow (limit 10) (genNatString (limit 10))
  runGenAndShow (limit 10) (genNatString (limit 10))
  runGenAndShow (limit 10) (genNatString (limit 10))
  
  putStrLn "\n=== Testing suchThat Combinator ==="
  putStrLn "Generating 3 even natural numbers:"
  
  runGenAndShow (limit 10) (genEvenNat (limit 10))
  runGenAndShow (limit 10) (genEvenNat (limit 10))
  runGenAndShow (limit 10) (genEvenNat (limit 10))
  
  putStrLn "=== All Combinator Tests Complete ==="
```

**What to do**: Add the `genEvenNat` generator and update main.

**What you'll notice**: `suchThat` filters results, only keeping those that satisfy the predicate.

## Step 6: Compile and run all combinator examples

Let's see all three combinators in action!

Compile your program:
```bash
idris2 Combinators.idr -o combinators
```

Run it:
```bash
./combinators
```

**What you should see**: Output demonstrating all three combinators:
```
=== Testing oneOf Combinator ===
Generating 5 colors from {Red, Green, Blue}:
✓ "Red"
✓ "Green"
✓ "Blue"
✓ "Red"
✓ "Green"

=== Testing map Combinator ===
Generating 3 natural numbers as strings:
✓ "42"
✓ "17"
✓ "3"

=== Testing suchThat Combinator ===
Generating 3 even natural numbers:
✓ 8
✓ 2
✓ 14

=== All Combinator Tests Complete ===
```

**What this shows you**: Each combinator serves a different purpose in customizing generation behavior.

## Step 7: Experiment with combinator combinations

Try combining multiple combinators:

1. **Combine oneOf and map**: Create a generator that chooses between different transformations
2. **Combine suchThat with other generators**: Filter results from complex generators
3. **Try different predicates**: Experiment with various filtering conditions

## What we accomplished

Congratulations! You've successfully explored DepTyCheck's basic combinators.

**Key achievements**:
- ✅ Used `oneOf` for explicit value choices
- ✅ Applied `map` for value transformation
- ✅ Used `suchThat` for result filtering
- ✅ Combined generators in practical examples

**Key concepts you've learned**:
- How to customize generator behavior beyond `deriveGen`
- The purpose and use cases for each combinator
- How combinators compose to create complex generators
- When to choose which combinator for specific tasks

## Next steps

Ready for more advanced topics? Try these:

- **Tutorial 5**: Understanding Generator Emptiness - Learn about type-level guarantees
- **Tutorial 6**: Tuning Constructor Probabilities - Control generation distribution
- **Experiment**: Create generators for your own custom data types using combinators

Remember: Combinators are your toolkit for when `deriveGen` alone isn't enough. They give you precise control over test data generation!

---

*This tutorial follows Diataxis principles by providing hands-on experimentation with clear, actionable examples.*

### What we accomplished
Congratulations! You've significantly enhanced your `DepTyCheck` toolkit by learning to use fundamental generator combinators.

You have learned to:
- **`oneOf`**: Make explicit choices among a set of values or generators.
- **`map`**: Transform generated values from one type or format to another.
- **`suchThat`**: Filter generated values to satisfy arbitrary predicates.

These combinators provide powerful means to customize and fine-tune your `DepTyCheck` generators, allowing you to create highly specific and targeted test data critical for effective property-based testing.

### Next steps
To further enhance your `DepTyCheck` skills, consider these tutorials:
- **Understanding Generator Emptiness: `NonEmpty` and `MaybeEmpty`**: Dive deeper into the type-level guarantees around generator success.
- **Advanced `Gen` Composition: Chaining and Transforming Values**: Explore more complex combinations and monadic patterns for building sophisticated generators.

Or, experiment further with what you've learned:
- Try combining `map` and `suchThat`: for example, generate odd numbers and then map them to their string representation.
- Create a generator using `oneOf` where some alternatives use `suchThat` to add specific conditions to individual choices.
- Explore the `Monad` instance for `Gen` to sequence generators where the output of one influences the input of the next.