# Mastering Dependent Generation: Controlling Argument Order

## What We'll Accomplish
In this tutorial, we'll learn how to control the order in which constructor arguments are generated, which is crucial for dependent types. By the end, you'll:
- Understand why argument generation order matters
- Use `GenOrderTuning` to specify custom generation sequences
- Handle complex dependencies in dependent types
- Have a working example demonstrating argument order control

## Prerequisites
Before we begin, make sure you have:
- Completed the "Generate Test Data for a Simple Type with `deriveGen`" tutorial
- Basic understanding of dependent types in Idris
- Idris 2 installed and DepTyCheck available in your project

## Step 1: Create a Dependent Type

Let's start with a simple dependent type where argument order matters. Create a new file called `ArgumentOrder.idr`:

```idris
module ArgumentOrder

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.Nat

%language ElabReflection

data SizedList : Nat -> Type -> Type where
  SNil : SizedList Z a
  SCons : {n : Nat} -> (x : a) -> SizedList n a -> SizedList (S n) a

genSizedList : (size : Nat) -> Fuel -> Gen MaybeEmpty (SizedList size Nat)
genSizedList size fuel = deriveGen

main : IO ()
main = do
  putStrLn "Generating sized lists:"
  let results = take 5 $ unGen1 (limit 10) (genSizedList 3 (limit 10))
  traverse_ (putStrLn . show) results
```

**Expected result**: You should see lists of exactly 3 natural numbers.

**What to notice**: The size parameter determines what kind of list we generate.

## Step 2: Observe Default Generation Order

Let's create a more complex type where argument dependencies are explicit:

```idris
-- Add to your existing file
data DependentPair : (a : Type) -> (a -> Type) -> Type where
  MkDP : (x : a) -> (y : b x) -> DependentPair a b

genDependentPair : Fuel -> Gen MaybeEmpty (DependentPair Nat (\n => Fin n))
genDependentPair fuel = deriveGen

testDependentPair : IO ()
testDependentPair = do
  putStrLn "Generating dependent pairs:"
  let results = take 3 $ unGen1 (limit 10) genDependentPair
  traverse_ (putStrLn . show) results

main : IO ()
main = do
  putStrLn "Generating sized lists:"
  let results = take 5 $ unGen1 (limit 10) (genSizedList 3 (limit 10))
  traverse_ (putStrLn . show) results
  
  putStrLn "\n"
  testDependentPair
```

**Expected result**: You should see pairs where the second element's type depends on the first element's value.

**What to notice**: DepTyCheck automatically handles the dependency - it generates the Nat first, then generates a Fin of that size.

## Step 3: Implement Custom Argument Order

Now let's create a type where we need explicit control over generation order:

```idris
-- Add to your existing file
import Deriving.DepTyCheck.Gen.Tuning
import Language.Reflection.Compat

data ComplexType : Type where
  MkComplex : (flag : Bool) -> (size : Nat) -> 
             (if flag then Nat else String) -> ComplexType

genComplexType : Fuel -> Gen MaybeEmpty ComplexType
genComplexType = deriveGen

instance GenOrderTuning "MkComplex".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [ConArgIdx 0, ConArgIdx 1]  -- Generate flag first, then size

testComplexType : IO ()
testComplexType = do
  putStrLn "Generating complex types with custom order:"
  let results = take 5 $ unGen1 (limit 10) genComplexType
  traverse_ (putStrLn . show) results

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\nGenerating complex types with custom order:"
  testComplexType
```

**Expected result**: You should see complex types where the flag and size are generated before the dependent field.

**What to notice**: We specify that the flag (argument 0) and size (argument 1) should be generated before the dependent field.

## Step 4: Handle Multiple Dependencies

Let's create a more sophisticated example with multiple interdependent arguments:

```idris
-- Add to your existing file
data MultiDependent : Type where
  MkMulti : (base : Nat) -> (offset : Nat) -> 
            (total : Nat) -> 
            (if base + offset == total then String else Bool) -> MultiDependent

genMultiDependent : Fuel -> Gen MaybeEmpty MultiDependent
genMultiDependent = deriveGen

instance GenOrderTuning "MkMulti".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [ConArgIdx 0, ConArgIdx 1, ConArgIdx 2]  -- Generate all Nat args first

testMultiDependent : IO ()
testMultiDependent = do
  putStrLn "Generating multi-dependent types:"
  let results = take 5 $ unGen1 (limit 10) genMultiDependent
  traverse_ (putStrLn . show) results

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\nGenerating multi-dependent types:"
  testMultiDependent
```

**Expected result**: You should see types where all numeric arguments are generated before the dependent field.

**What to notice**: We ensure all the arguments needed for the condition are generated first.

## What We Accomplished

Congratulations! We've successfully learned how to control argument generation order:
- Created dependent types where argument order matters
- Implemented custom generation order with `GenOrderTuning`
- Handled complex dependencies with multiple interdependent arguments

You now have the tools to ensure your generators produce valid data even for complex dependent types.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Generating GADT Constructors
- How-to: Debugging Generator Derivation Issues
- Explanation: How DepTyCheck Infers Dependencies

Or experiment by creating types with circular dependencies and see how argument order tuning helps resolve them.