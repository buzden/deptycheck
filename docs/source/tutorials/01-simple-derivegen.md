# Generating Test Data for a Simple Type with `deriveGen`

## Introduction

In this tutorial, we will create and use a simple data type generator with DepTyCheck. We'll define a basic traffic light type and use `deriveGen` to automatically create a generator that can produce random traffic light values.

By the end of this tutorial, you will have:
- A working Idris file with automatic data generation
- An understanding of how `deriveGen` creates generators
- Practical experience running and observing generated data

### What we'll build together
Today we'll create a `TrafficLight` data type that can randomly generate red, yellow, or green traffic light states. You'll see how DepTyCheck handles the complexity of generator creation automatically.

**Expected learning time**: 15-20 minutes

## Prerequisites

Before we begin, let's make sure you have everything you need:

- **Idris 2** (version 0.6.0 or newer)
- Basic familiarity with Idris syntax and data types
- DepTyCheck library installed (`pack install deptycheck`)
- A text editor and terminal ready

If you haven't installed DepTyCheck yet, open your terminal and run:
```bash
pack install deptycheck
```

## Step 1: Create your first data type

Let's start by creating a simple traffic light data type. This will be our foundation for learning generator derivation.

First, create a new file called `TrafficLight.idr` and add this code:

```idris
module TrafficLight

data TrafficLight = Red | Yellow | Green
```

**What to do**: Copy this exact code into your new file.

**Expected result**: You should have a file named `TrafficLight.idr` containing this simple enumeration.

**What you've accomplished**: You've defined an Algebraic Data Type (ADT) - a fundamental building block in functional programming. Each constructor (`Red`, `Yellow`, `Green`) represents a possible state of our traffic light.

## Step 2: Enable metaprogramming and import DepTyCheck

Now we'll prepare the file to use DepTyCheck's automatic generation features. We need to enable elaboration reflection and import the necessary modules.

Replace your file contents with this updated version:

```idris
module TrafficLight

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen

data TrafficLight = Red | Yellow | Green
```

**What to do**: Replace your existing code with this enhanced version.

**Expected result**: Your file now includes the tools needed for generator derivation.

**What you'll notice**:
- `%language ElabReflection` tells Idris we're using metaprogramming features
- `Data.Fuel` imports fuel-based recursion control (essential for generation)
- `Test.DepTyCheck.Gen` gives us the `Gen` type and `deriveGen` macro

## Step 3: Derive your first generator

Now for the magic! We'll use `deriveGen` to automatically create a generator for our TrafficLight type.

Add this line to your file:

```idris
module TrafficLight

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen

data TrafficLight = Red | Yellow | Green

genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
genTrafficLight = deriveGen
```

**What to do**: Add the `genTrafficLight` function declaration.

**Expected result**: Your file should compile without errors when you check it.

**What you've accomplished**: You've told DepTyCheck to automatically generate code that can produce random TrafficLight values. The `deriveGen` macro analyzes your type signature and creates the implementation for you.

**Notice how**: The type signature `Fuel -> Gen MaybeEmpty TrafficLight` tells DepTyCheck exactly what we want - a function that takes fuel and returns a TrafficLight generator.

## Step 4: Run your generator and see results

Let's make our generator produce actual values so we can see it working.

Add this final section to your file:

```idris
module TrafficLight

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen
import Control.Monad.RWS
import Control.Monad.Random

data TrafficLight = Red | Yellow | Green

genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
genTrafficLight = deriveGen

-- Helper to run generator once
runTrafficLightGen : IO TrafficLight
runTrafficLightGen = do
  seed <- getRandomSeed
  let (value, _) = runRandom seed (runGen (limit 10) genTrafficLight)
  case value of
    Nothing => fail "Generator produced empty result!"
    Just v  => pure v

main : IO ()
main = do
  putStrLn "--- Generating 5 TrafficLight values ---"
  
  -- Generate and display 5 random traffic lights
  tl1 <- runTrafficLightGen
  putStrLn $ "First light:  " ++ show tl1
  
  tl2 <- runTrafficLightGen
  putStrLn $ "Second light: " ++ show tl2
  
  tl3 <- runTrafficLightGen
  putStrLn $ "Third light:  " ++ show tl3
  
  tl4 <- runTrafficLightGen
  putStrLn $ "Fourth light: " ++ show tl4
  
  tl5 <- runTrafficLightGen
  putStrLn $ "Fifth light:  " ++ show tl5
  
  putStrLn "----------------------------------------"
```

**What to do**: Replace your file contents with this complete version.

**Expected result**: You now have a complete, runnable Idris program.

## Step 5: Compile and run your program

Now let's see your generator in action!

First, compile your program:
```bash
idris2 TrafficLight.idr -o trafficlight
```

Then run it:
```bash
./trafficlight
```

**What you should see**: Output similar to this (colors may vary due to randomness):
```
--- Generating 5 TrafficLight values ---
First light:  Red
Second light: Green
Third light:  Yellow
Fourth light: Red
Fifth light:  Green
----------------------------------------
```

**What this shows you**: Your `deriveGen` call successfully created a working generator! Each run will produce different combinations of Red, Yellow, and Green lights.

**If you see errors**: Make sure DepTyCheck is installed correctly and all imports are spelled exactly as shown.

## Step 6: Experiment and observe

Try making small changes to see how the generator behaves:

1. **Change the number of generations**: Modify `main` to generate more or fewer traffic lights
2. **Add a new constructor**: Add `FlashingRed` to your `TrafficLight` type and recompile
3. **Change fuel**: Try `limit 5` instead of `limit 10` in the `runTrafficLightGen` helper

**Notice how**: Each change affects the output. Adding `FlashingRed` will automatically make it appear in the generated values!

## What we accomplished

Congratulations! You've successfully created your first automatic generator with DepTyCheck.

**Key achievements**:
- ✅ Defined a simple data type in Idris
- ✅ Used `%language ElabReflection` for metaprogramming
- ✅ Imported DepTyCheck modules successfully
- ✅ Applied `deriveGen` to automatically create a generator
- ✅ Compiled and ran a working generator
- ✅ Observed random data generation in action

**Key concepts you've learned**:
- How DepTyCheck uses metaprogramming to analyze types
- The role of `Fuel` in controlling generator behavior
- The difference between `Gen MaybeEmpty` and `Gen NonEmpty`
- How to run generators and extract their values

## Next steps

Ready to build on this foundation? Here are your next learning opportunities:

- **Tutorial 2**: Property Testing a List Sorting Function - Learn how to test real functions
- **Tutorial 3**: Controlling Recursion in Generated Data - Explore how Fuel works with recursive types
- **Experiment more**: Try creating generators for other simple types like `Bool`, `Nat`, or custom enumerations

Remember: The most powerful part of DepTyCheck is that `deriveGen` works for much more complex types too - this simple example is just the beginning!

---

*This tutorial follows Diataxis principles by focusing on hands-on learning through concrete examples and immediate results.*



### Step 1: Define a Simple Enumeration Data Type
Let's begin by defining a straightforward data type. For this tutorial, we'll create a `TrafficLight` type, which is a simple enumeration representing the states of a traffic light. This type has no parameters or complex dependencies, making it an ideal starting point for demonstrating `deriveGen`.

First, open your text editor and create a new file. Save it as `TrafficLight.idr` in a convenient location (e.g., a new project directory). Then, add the following Idris code to it:

```idris
module TrafficLight

data TrafficLight = Red | Yellow | Green
```

**Expected result**: After saving, you should have a file named `TrafficLight.idr` containing the above code. Your Idris editor or IDE might highlight syntax, but no compilation is expected at this stage.

**What to notice**: This `TrafficLight` data type is a basic Algebraic Data Type (ADT) with three constructors: `Red`, `Yellow`, and `Green`. It's a fundamental concept in functional programming and serves as a perfect example for automatic data generation.

### Step 2: Enable Elaboration Reflection and Import `DepTyCheck` Components
`DepTyCheck` utilizes Idris 2's powerful *elaboration reflection* capabilities to automatically generate code for your generators. To use these features, we need to explicitly enable a language extension and import the necessary `DepTyCheck` modules. We also need `Data.Fuel` to manage potential recursion in generators (even simple ones implicitly use it for type consistency).

Modify your `TrafficLight.idr` file to include these additions:

```idris
module TrafficLight

%language ElabReflection -- Enables Idris's metaprogramming features

import Data.Fuel         -- Essential for controlling generator size/depth
import Test.DepTyCheck.Gen -- Provides the 'Gen' type and 'deriveGen'

data TrafficLight = Red | Yellow | Green
```

**Expected result**: Your file should still compile cleanly without errors. Your editor might now recognize the new keywords and imports.

**What to notice**: 
- `%language ElabReflection`: This directive tells the Idris compiler that you intend to use reflection features, which allow Idris code to analyze and generate other Idris code during compilation. `deriveGen` is a macro that relies heavily on this.
- `import Data.Fuel`: Even for simple types, `DepTyCheck`'s generators are parameterized by `Fuel`. This module provides the `Fuel` type, which is used internally to ensure that recursive data structures (like lists or trees) can be generated to a finite size. We'll explore `Fuel` in more detail in a later tutorial.
- `import Test.DepTyCheck.Gen`: This module contains the `Gen` data type (representing a test data generator) and, crucially, the `deriveGen` macro itself.

### Step 3: Automatically Derive the Generator with `deriveGen`
Now for the magic! We will declare the *type signature* for our `TrafficLight` generator, and then simply assign `deriveGen` to it. `DepTyCheck` will inspect this type signature and synthesize the entire generator implementation for us.

Add the `genTrafficLight` function declaration to your `TrafficLight.idr` file:

```idris
module TrafficLight

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen

data TrafficLight = Red | Yellow | Green

genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
genTrafficLight = deriveGen
```

**Expected result**: Upon saving or compiling, your `TrafficLight.idr` file should compile successfully. There will be no visible output about the generated code, but `DepTyCheck` has internally created an Idris function that can produce `TrafficLight` values.

**What to notice**: 
- `genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight`: This is the *declaration* of our generator function. It states that `genTrafficLight` takes a `Fuel` argument and returns a `Gen MaybeEmpty TrafficLight`. 
  - `Gen MaybeEmpty TrafficLight`: `Gen` is the core type for generators. `MaybeEmpty` is an *emptiness annotation*, indicating that this generator *might not* produce a value (though for a simple enumeration like `TrafficLight`, it almost certainly always will unless `Fuel` is severely constrained in more complex scenarios). We'll cover `Emptiness` in a dedicated tutorial.
- `genTrafficLight = deriveGen`: This is the *derivation entry point*. By writing this, you're instructing `DepTyCheck`'s elaboration reflection machinery to analyze the type signature of `genTrafficLight` and automatically generate its function body. `DepTyCheck` inspects `TrafficLight`, sees its constructors (`Red`, `Yellow`, `Green`), and creates code that randomly picks one of them. For primitive types like `Int`, `Char`, `String`, etc., `deriveGen` also works seamlessly, providing default generation strategies without requiring explicit definitions.

### Step 4: Run the Generator and Observe Output
To confirm our generator works, we need to run it and see the values it produces. This involves setting up a basic `IO` action that invokes the generator and prints its output. We'll also need some standard Idris modules for random number generation and monadic composition.

Further append the following code to your `TrafficLight.idr` file:

```idris
module TrafficLight

%language ElabReflection

import Data.Fuel
import Test.DepTyCheck.Gen -- Provides the 'Gen' type, 'runGen'
import Control.Monad.RWS    -- For the MonadRandom instance used by runGen
import Control.Monad.Random -- Provides getRandomSeed


data TrafficLight = Red | Yellow | Green

genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
genTrafficLight = deriveGen

-- runTrafficLightGen : IO TrafficLight
-- Helper function to run our generator once and extract its value.
-- This function abstracts away the randomness setup and handling of 'MaybeEmpty'.
runTrafficLightGen : IO TrafficLight
runTrafficLightGen = do
  -- Get a random seed to ensure different results on each run
  seed <- getRandomSeed
  
  -- Run the generator. 'runGen' takes Fuel and our generator.
  -- It produces a (Maybe a, g') tuple, where 'a' is our generated value
  -- and 'g'' is the updated random generator state.
  let (value, _) = runRandom seed (runGen (limit 10) genTrafficLight)
  
  -- Handle the 'MaybeEmpty' result. For TrafficLight, it should always produce a 'Just'.
  case value of
    -- If for some reason the generator produces 'Nothing' (e.g., if we were generating
    -- a type with no possible values, or if fuel ran out in a complex scenario),
    -- we'll indicate a failure.
    Nothing => fail "Generator produced Nothing! This should not happen for TrafficLight!"
    -- If a value is produced (which it should be), we return it.
    Just v  => pure v


main : IO ()
main = do
  putStrLn "--- Generating 5 TrafficLight values ---"
  putStrLn "(Each run will produce different results due to randomness)"
  
  -- Call our helper function five times to get and print TrafficLight values.
  -- Notice how 'Fuel' (here 'limit 10') ensures generation terminates, even for recursive types.
  tl1 <- runTrafficLightGen
  putStrLn $ show tl1
  
tl2 <- runTrafficLightGen
  putStrLn $ show tl2

tl3 <- runTrafficLightGen
putStrLn $ show tl3

tl4 <- runTrafficLightGen
putStrLn $ show tl4

tl5 <- runTrafficLightGen
putStrLn $ show tl5

putStrLn "----------------------------------------"
```

**Expected output**: After compiling and running, you will see output similar to this (the exact values will vary due to randomness):

```text
--- Generating 5 TrafficLight values ---
(Each run will produce different results due to randomness)
Red
Green
Yellow
Red
Green
----------------------------------------
```

To compile your program, open your terminal in the directory where `TrafficLight.idr` is saved and run:

```bash
idris2 TrafficLight.idr -o trafficlightgen
```

Then, to execute the compiled program, run:

```bash
./trafficlightgen
```

**What to notice**: 
- `getRandomSeed`: Used to initialize the random number generator, ensuring that each execution of the program produces a different sequence of random values.
- `runRandom seed (runGen (limit 10) genTrafficLight)`: This is the core call to execute our `Gen`erator. 
  - `runGen`: This function from `Test.DepTyCheck.Gen` is responsible for extracting a value from the `Gen` monad. It requires a `Fuel` argument.
  - `(limit 10)`: This provides an initial `Fuel` budget. For simple, non-recursive types like `TrafficLight`, the specific number doesn't matter much, but it's crucial for controlling the size of recursive data structures, preventing infinite loops. A larger number generally allows for larger generated values. You can experiment by changing this value.
- The output clearly demonstrates that `deriveGen` successfully created a generator that produces valid instances of our `TrafficLight` data type. Furthermore, `DepTyCheck` implicitly handles primitive types such as `Nat`, `Int`, `Bool`, etc., with `deriveGen`, making it highly versatile.

### What we accomplished
Congratulations! You've successfully completed your first journey into `DepTyCheck`'s automatic generation capabilities.

Here’s a recap of what you’ve learned:
- **Defined an Idris 2 Algebraic Data Type**: You created `TrafficLight` to model a simple real-world concept.
- **Enabled Elaboration Reflection**: You understood the need for `%language ElabReflection` to power `DepTyCheck`'s macros.
- **Used `deriveGen`**: You successfully employed the `deriveGen` macro to automatically create a test data generator for `TrafficLight` with minimal manual effort.
- **Executed and Observed a Generator**: You ran the generated code and saw it produce diverse (random) instances of your data type.

This fundamental understanding is your stepping stone to leveraging the full power of `DepTyCheck` for robust property-based testing of complex, dependently-typed systems.

### Next steps
Ready to deepen your `DepTyCheck` expertise? We recommend checking out these follow-up tutorials:
- **Property Testing a List Sorting Function**: Learn how to write and run actual property tests against your code.
- **Controlling Recursion in Generated Data (e.g., for Trees)**: Dive deeper into the `Fuel` mechanism and how it tames recursive data structures.

Or, feel free to experiment with what you've learned:
- Try adding more constructors to your `TrafficLight` data type (e.g., `FlashingRed`) and observe how `deriveGen` automatically adapts.
- Create a new file with a different simple ADT (e.g., `Feeling = Happy | Sad | Neutral`) and generate values for it.