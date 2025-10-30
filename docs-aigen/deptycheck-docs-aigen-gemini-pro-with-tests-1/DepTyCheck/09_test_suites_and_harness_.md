# Chapter 9: Test Suites and Harness

In the [previous chapter](08_model_coverage_analysis_.md), we learned how to add sensors to our generator factory to track what's being produced, ensuring we have good test data coverage. We now have a complete toolbox: we can automatically create generators with [deriveGen](02_derivegen__the_automatic_generator_factory_.md), fine-tune them with [Derivation Tuning](07_derivation_tuning_.md), and check their output with [Model Coverage Analysis](08_model_coverage_analysis_.md).

Now for the final piece of the puzzle: How do we package all of this into a robust, automated quality assurance system? A `DepTyCheck` user relies on these generators to be correct. How do *we*, the developers of `DepTyCheck`, ensure that our factory isn't faulty?

Welcome to the `DepTyCheck` Quality Assurance (QA) department. In this chapter, we'll explore the extensive testing infrastructure that makes sure the generator factory itself works exactly as advertised.

## The Problem: How Do You Test a Test Tool?

We have a factory that produces data generators. But what if there's a bug in the factory?
*   What if a change to `deriveGen` suddenly causes it to produce incorrect or less efficient code?
*   What if a generator that's supposed to produce booleans with a 50/50 probability starts producing `True` 90% of the time?
*   What if a generator works fine on its own, but crashes when integrated into a larger program?

We need a multi-layered testing strategy to catch all these different kinds of problems. `DepTyCheck`'s test suite isn't just a handful of simple tests; it's a comprehensive system with several specialized "inspectors," each with a different job.

## Meet the QA Team

Think of the `DepTyCheck` test suite as a team of QA inspectors for our generator factory. Each one has a very specific task.

1.  **The Blueprint Inspector ("print" tests):** This inspector checks the *instructions* that `deriveGen` produces, not the final random data. It ensures the generated code itself doesn't change unexpectedly. This is called **Golden Testing**.
2.  **The Product Tester ("run" tests):** This inspector takes a generator, runs it to produce actual data, and makes sure nothing crashes. This is a classic **Integration Test**.
3.  **The Statistician ("distribution" tests):** This inspector runs a generator millions of times and performs a statistical analysis to verify that the random data is produced with the correct probabilities.

Let's meet each of them and see how they work.

### 1. Golden Testing: The "print" Inspector

The most unique and powerful type of test in `DepTyCheck` is the "golden test." Its job is to detect any unintended changes in the code that [`deriveGen`](02_derivegen__the_automatic_generator_factory_.md) produces.

Imagine `deriveGen` is a machine that prints blueprints. For a given data type, we expect it to print the same blueprint every time. A golden test works by:
1.  Running `deriveGen` to produce the blueprint (the generator code).
2.  Saving a copy of this blueprint as a "golden file" (a text file with a `.out` extension).
3.  On all future test runs, it generates a new blueprint and compares it to the golden copy. If there are *any* differences, the test fails, warning us that something has changed.

This is incredibly effective for catching regressions. If a small "improvement" to `deriveGen` accidentally makes the generated code for `Vect` twice as long and less efficient, the golden test will immediately fail, showing us a "diff" of the old and new code.

### 2. Integration Testing: The "run" Inspector

While golden tests check the *code*, "run" tests check the *runtime behavior*. Their job is simple but crucial: take a derived generator, run it a few times, and make sure it doesn't crash.

This is a sanity check that ensures the generated code is not only correct-looking but also executable.

Here’s a simplified version of a runner file used for these tests. It defines a helper that takes a list of generators, runs each one a few times, and prints the results.

```idris
-- From: tests/derivation/_common/RunDerivedGen.idr

-- `GenForRun` is a helper to hold any generator that can show its values.
data GenForRun : Type where
  G : Show x => (Fuel -> Gen MaybeEmpty x) -> GenForRun

-- This function runs a list of generators and prints some values.
runGs : List GenForRun -> IO Unit
runGs checkedGens = do
  putStrLn "Generated values:"
  for_ checkedGens \(G gen) => do
    let values = unGenTryN 10 someStdGen (gen (limit 20))
    print values
    putStrLn "-----"
```
This is a straightforward integration test. If `unGenTryN` were to crash because of a bug in `gen`, the test would fail.

### 3. Statistical Testing: The "distribution" Inspector

This is the most sophisticated inspector. If we have a generator that is supposed to be fair—like a coin flip—how can we be sure it is? We can't just check one or two results. We need to check many thousands, or even millions, of results and analyze them statistically.

`DepTyCheck` has built-in tools for exactly this. Consider a simple `Bool` generator. We expect it to produce `True` and `False` with equal probability (50% each). A statistical test will:
1. Run the `Bool` generator millions of times.
2. Count the number of `True`s and `False`s.
3. Use statistical formulas to calculate if the observed ratio (e.g., 49.998% `True`s) is "close enough" to the expected 50% to be statistically sound.

The tooling for this is quite advanced, but the high-level usage is straightforward.

```idris
-- From: tests/lib/distribution/with-empty-001/DistrCheckCommon.idr

-- A function that runs a generator many times and verifies its distribution
-- against a set of coverage conditions.
verdict : Gen em a -> Vect n (CoverageTest a) -> Maybe (Vect n SignificantBounds)
verdict gen conds =
  -- `unGenTryN 10000000` runs the generator ten million times!
  find . checkCoverageConditions conds . unGenTryN 10000000 someStdGen

-- A helper to print the verdict.
printVerdict : Gen em a ->

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)