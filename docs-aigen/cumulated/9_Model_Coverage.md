# Chapter 9: Model Coverage Analysis

## Introduction

In previous chapters, we've learned how to create powerful generators using `deriveGen` and tune them for specific testing needs. But this raises a crucial question: how do we know our generators are actually producing diverse, comprehensive test data?

Model Coverage Analysis is `DepTyCheck`'s built-in quality assurance system that gives you detailed reports on what your generators are actually creating. It helps you identify blind spots in your testing and ensures your property-based tests are truly thorough.

## Learning Objectives

In this chapter, we will:
- Understand the problem of test data blind spots
- Learn how to instrument generators with coverage tracking
- Generate and interpret coverage reports
- Explore the internal mechanisms that make coverage analysis work
- Apply coverage analysis to real-world testing scenarios

## Prerequisites

Before starting, you should be familiar with:
- Basic `DepTyCheck` generator creation using `deriveGen`
- The `Gen` monad and its basic operations
- Running generators with fuel and random seeds

## Understanding the Problem: Test Data Blind Spots

### The Risk of Incomplete Testing

Imagine you're testing a function that processes different types of user input:

```idris
data UserInput = TextInput String | FileUpload String | VoiceCommand String
```

You create a generator and run 100 tests. All tests pass successfully. But what if your generator accidentally only produces `TextInput` values? You'd never test the `FileUpload` or `VoiceCommand` paths, leaving potential bugs undiscovered in those code paths.

### Exercise: Identify Potential Blind Spots

Consider this generator for a simple data type:

```idris
data TrafficLight = Red | Amber | Green

genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
genTrafficLight = deriveGen
```

**Question**: What could go wrong if this generator develops a bias?

**Solution**: If the generator is biased and rarely produces `Amber` values, your tests might miss bugs in the code that handles amber lights. For example, timing logic or state transitions specific to the amber phase could contain undetected errors.

## Instrumenting Generators for Coverage Analysis

### The `withCoverage` Macro

The foundation of coverage analysis is the `withCoverage` macro. It wraps any generator and adds automatic tracking of which constructors are being generated.

```idris
import Test.DepTyCheck.Gen.Coverage

-- Standard generator
genLight : Fuel -> Gen MaybeEmpty TrafficLight
genLight = deriveGen

-- Instrumented generator with coverage tracking
genLightWithCoverage : Fuel -> Gen MaybeEmpty TrafficLight
genLightWithCoverage = withCoverage genLight
```

### How `withCoverage` Works

When you wrap a generator with `withCoverage`, `DepTyCheck` automatically injects code that:
1. Runs the original generator
2. Examines the resulting value
3. Adds a label identifying the constructor used
4. Returns the original value unchanged

This happens transparently at compile time, so your generator's behavior remains the same—it just gains coverage tracking capabilities.

## Generating and Interpreting Coverage Reports

### The Three-Step Process

Creating a coverage report involves three simple steps:

1. **Initialize** a coverage report template
2. **Generate** data and collect coverage information
3. **Analyze** and display the results

### Step 1: Initialize Coverage Information

Use `initCoverageInfo` to create an empty report template. This function creates a "blueprint" of your type - it inspects the generator's return type and prepares slots for tracking each constructor:

```idris
import Test.DepTyCheck.Gen.Coverage

-- Create an empty coverage report for our generator
initialReport : CoverageGenInfo TrafficLight
initialReport = initCoverageInfo genLight
```

This macro inspects your generator's type signature at compile time and creates a structure that knows about all possible constructors. For our `TrafficLight` example, it would create tracking slots for `Red`, `Amber`, and `Green`, all initialized to zero counts.

### Step 2: Generate Data and Collect Coverage

Use `unGenTryND` to run your instrumented generator multiple times:

```idris
import Data.List.Lazy
import System.Random.Pure.StdGen

-- Generate 100 values with coverage tracking
results : LazyList (ModelCoverage, TrafficLight)
results = unGenTryND 100 someStdGen (genLightWithCoverage (limit 10))
```

### Step 3: Analyze and Display Results

Combine the individual coverage results into a final report:

```idris
-- Combine all coverage data
finalCoverage : ModelCoverage
finalCoverage = foldl (<+>) neutral (map fst results)

-- Register coverage in the final report
finalReport : CoverageGenInfo TrafficLight
finalReport = registerCoverage finalCoverage initialReport

-- Display the results
main : IO ()
main = putStrLn $ show finalReport
```

### Exercise: Create a Complete Coverage Report

Write a complete program that generates and displays coverage information for a simple data type:

```idris
data Message = Text String | Image String | Audio String

genMessage : Fuel -> Gen MaybeEmpty Message
genMessage = deriveGen

genMessageWithCoverage : Fuel -> Gen MaybeEmpty Message
genMessageWithCoverage = withCoverage genMessage
```

**Solution**:
```idris
main : IO ()
main = do
  let initialReport = initCoverageInfo genMessage
  let results = unGenTryND 100 someStdGen (genMessageWithCoverage (limit 10))
  let finalCoverage = foldl (<+>) neutral (map fst results)
  let finalReport = registerCoverage finalCoverage initialReport
  putStrLn $ show finalReport
```

## Interpreting Coverage Reports

### Understanding Report Output

A typical coverage report provides clear, actionable information. Let's analyze a sample report:

```
TrafficLight covered partially (100 times)
  - Red: covered (45 times)
  - Amber: covered (55 times)
  - Green: not covered
```

Key elements to understand:
- **"covered fully" vs "covered partially"**: Indicates if all constructors were generated
- **Parenthetical counts**: Show total number of generated values
- **Individual constructor status**: Shows counts for each constructor
- **"not covered"**: Highlights constructors that were never generated

### Exercise: Analyze a Coverage Report

Given this report for a user input system:

```
UserInput covered partially (200 times)
  - TextInput: covered (150 times)
  - FileUpload: covered (50 times)
  - VoiceCommand: not covered
```

**Question**: What does this tell you about the generator and what actions should you take?

**Solution**: The generator has a strong bias toward `TextInput` values (75% of generated data) and completely misses `VoiceCommand` inputs. This indicates:
- The generator needs tuning to balance constructor weights
- There may be constraints preventing `VoiceCommand` generation
- Your tests are missing coverage for voice command functionality

## Advanced Coverage Analysis Techniques

### Coverage for Complex Types

Coverage analysis works seamlessly with complex, nested types. Consider this expression language:

```idris
data Tree a = Leaf a | Node (Tree a) (Tree a)

genTree : Fuel -> Gen MaybeEmpty (Tree Nat)
genTree = deriveGen
```

When you run coverage analysis on `genTree`, you'll get reports for both `Tree` constructors (`Leaf` and `Node`) and the nested `Nat` type.

### Automatic Coverage with `deriveGen`

Generators created with `deriveGen` have a special advantage: they're automatically instrumented for coverage analysis. You don't need to manually add `withCoverage` unless you're using custom or handwritten generators.

```idris
data Expression = 
    Number Nat 
  | Add Expression Expression 
  | Multiply Expression Expression

genExpression : Fuel -> Gen MaybeEmpty Expression
genExpression = deriveGen
```

Even without explicitly calling `withCoverage`, `genExpression` will track coverage information when analyzed with the coverage reporting functions.

## Internal Mechanisms: How Coverage Tracking Works

### The Compile-Time Transformation

When `withCoverage` instruments your generator, it performs a compile-time transformation. For example:

```idris
-- Original generator
pure Red

-- Becomes conceptually
do
  val <- pure Red
  label "Red" (pure val)
```

### The `ModelCoverage` Data Structure

At the core of coverage tracking is the `ModelCoverage` type:

```idris
record ModelCoverage where
  constructor MkModelCoverage
  unModelCoverage : SortedMap Label Nat
```

This simple but efficient structure tracks how many times each label (constructor) has been encountered during generation.

### The Writer Monad Pattern

Coverage analysis uses the `Writer` monad pattern to track labels without disrupting the main generation logic. When you run:

```idris
unGenD genLightWithCoverage
```

The function runs your generator inside a `WriterT ModelCoverage` context, which accumulates labels transparently.

### Exercise: Trace the Transformation

Trace how `withCoverage` would transform this generator:

```idris
genComplex : Fuel -> Gen MaybeEmpty (Either String Nat)
genComplex fl = oneOf [Left <$> string, Right <$> nat]
```

**Solution**: The transformation would add labeling for both `Left` and `Right` constructors:

```idris
do
  val <- oneOf [Left <$> string, Right <$> nat]
  case val of
    Left s => label "Left" (pure (Left s))
    Right n => label "Right" (pure (Right n))
```

## Practical Applications and Best Practices

### Finding and Fixing Generator Biases

Coverage analysis is excellent for detecting unintentional biases in your generators. Consider this scenario:

```
Shape covered partially (100 times)
  - Circle: covered (90 times)
  - Square: covered (10 times)
  - Triangle: not covered
```

**Exercise**: How would you improve this generator?

**Solution**: Use derivation tuning to increase the weight of `Square` and ensure `Triangle` is included. You might need to:
- Check if `Triangle` has constraints that prevent generation
- Use `weight` to balance constructor probabilities
- Verify that all constructor arguments can be generated

### Ensuring Test Completeness

Before declaring your tests complete, run coverage analysis to ensure all code paths are being exercised. This is especially important for:
- Critical business logic paths
- Error handling code
- Boundary conditions
- Less frequently used features

### When to Use Coverage Analysis

- **After creating new generators**: Verify they work as expected
- **When tests pass unexpectedly**: Check if you're missing important cases
- **During generator tuning**: Monitor the impact of your changes
- **In continuous integration**: Catch generator issues early

### Performance Considerations

Coverage analysis adds minimal overhead. The labeling happens during generation, and the analysis is efficient even for large test runs.

## Summary

In this chapter, we've explored `DepTyCheck`'s powerful Model Coverage Analysis system. We learned:

- **Why coverage matters**: Blind spots in test data can hide bugs
- **How to instrument generators**: Using `withCoverage` to add tracking
- **Generating reports**: The three-step process of initialization, generation, and analysis
- **Internal mechanisms**: How the system works under the hood

Coverage analysis transforms property-based testing from "hope it's good enough" to "know it's thorough."

## Next Steps

Now that you can verify your generators are producing diverse test data, you're ready to explore more advanced `DepTyCheck` features. In the next chapter, we'll look at how `DepTyCheck` manages generator signatures and finds the right generators for complex type hierarchies.