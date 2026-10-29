# 10. Advanced Derivation Tuning

In the last tutorial, we saw how to use `deriveGen` and provide it with custom generators for base types like `String`. However, `DepTyCheck` offers
even deeper, more powerful mechanisms for controlling the derivation process for situations where just providing a generator isn't enough.

```{warning}
**This is an Advanced Tutorial.** The tuning mechanism uses some of Idris's more powerful features, specifically compile-time reflection
and type class instances. We will walk through it step-by-step, but a full explanation of these concepts is beyond the scope of this tutorial. If you
just want to use `deriveGen` with its default settings and provide external generators, you can safely skip this lesson.
```

## Our Goal

We will tackle two common problems that cannot be solved with external generators alone:

1. Fixing Bias: We will prove that a default generator is biased and then implement the `ProbabilityTuning` interface to change the frequency of a
specific constructor.
2. Fixing Inefficiency: We will show how a naive generator for a constrained type is inefficient and then implement the `GenOrderTuning` interface to
guide the derivation logic and make it robust.

## Prerequisites

- Completion of [Automatic Generator Derivation](t04-automatic-generator-derivation.md).
- A willingness to engage with some advanced Idris concepts!

---

## Step 1: Discovering a Biased Generator

Let's start by defining a simple, recursive data type where the default `deriveGen` strategy will produce a biased result.

### Create a new file named `TuningTutorial.idr`

```idris
import Deriving.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen.Tuning -- For the tuning interfaces
import Data.Fuel
import Data.So

-- From previous tutorials
import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage
import System.Random.Pure.StdGen

%language ElabReflection

%hint
genStr : Gen MaybeEmpty String
genStr = elements ["a", "b", "c", "d", "f", "g", "h"]
```

### Add the following code

```idris
mutual
  data EntryList : Type where
    Nil : EntryList
    (::) : Entry -> EntryList -> EntryList

  data Entry = File String | Directory EntryList

-- A generator for Entry that takes an external String generator
genEntry : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty Entry
genEntry = deriveGen
```

### Add a coverage analysis `main` function

```idris
main : IO ()
main = do
  let reportTemplate = initCoverageInfo genEntry
  let rawCoverageRuns = unGenTryND 1000 someStdGen (genEntry (limit 10))
  let allRawCoverage = concatMap fst rawCoverageRuns
  let finalReport = registerCoverage allRawCoverage reportTemplate
  putStrLn $ show finalReport
```

### Analyze the report

The results will be starkly imbalanced because `deriveGen` prefers the non-recursive `File` constructor

```text
    Entry covered fully (1000 times)
      - File: covered (909 times)
      - Directory: covered (91 times)
```

This is the problem we need to solve.

---

## Step 2: Probability Tuning

To fix the bias, we must implement the `ProbabilityTuning` interface for the `Directory` constructor. This tells `deriveGen` to override its default
weight.

### Define the implementation

Place this implementation at the top level of your file. It targets the `Directory` constructor by its name

```idris
mutual
  data EntryListP : Type where
    Nil2 : EntryListP
    Q2 : EntryP -> EntryListP -> EntryListP

  data EntryP = FileP String | DirectoryP EntryListP

-- A generator for Entry that takes an external String generator
genEntryP : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty EntryListP
genEntryP = deriveGen

ProbabilityTuning `{DirectoryP}.dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = 1
```

- `ProbabilityTuning ... where`: We define a specific implementation of this interface for a constructor.
- `"Directory".dataCon`: This is a `Name` literal that refers to the `Directory` constructor. Since `Directory` is defined in this same file, we can use
the simple name without a module prefix.
- `isConstructor = itIsConstructor`: This is a required line of reflection boilerplate that confirms we have targeted a valid constructor.
- `tuneWeight _ = 10`: We implement the `tuneWeight` function. It takes the default weight `_` and we ignore it, always returning our new, higher weight
of `10`.

### Re-run the coverage analysis

The compiler will now automatically find and apply our implementation. Simply recompile and run.

```idris
mainP : IO ()
mainP = do
  let reportTemplate = initCoverageInfo genEntryP
  let rawCoverageRuns = unGenTryND 1000 someStdGen (genEntryP (limit 10))
  let allRawCoverage = concatMap fst rawCoverageRuns
  let finalReport = registerCoverage allRawCoverage reportTemplate
  putStrLn $ show finalReport
```

### Analyze the new report

The distribution will now be much closer to a 50/50 balance, proving we have successfully tuned the probability.

```text
    Entry covered fully (1000 times)
      - File: covered (526 times)
      - Directory: covered (474 times)
```

---

## Step 3: Generation Order Tuning

Probability isn't the only thing we can tune. For some dependent types, the _order_ in which arguments are generated is critical for efficiency.
Consider a pair `(n, m)` where we require `n < m`.

```idris
data LtPair : Type where
  MkLtPair : (n : Nat) -> (m : Nat) -> (prf : So $ n < m) -> LtPair
```

`deriveGen`'s default strategy might randomly pick `n=10` and `m=5`, then fail because it can't prove `10 < 5`. This is very inefficient. We can tell it
to generate `m` first, making it much easier to pick a valid `n`.

### Define the generator and the tuning implementation in your file

```idris
GenOrderTuning `{MkLtPair}.dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{m}]

genLtPair : Fuel -> Gen MaybeEmpty LtPair
genLtPair = deriveGen

Show LtPair where
  show (MkLtPair n m _) = "MkLtPair " ++ show n ++ " " ++ show m ++ " _"
```

- `GenOrderTuning ... where`: We implement the ordering interface for the `MkLtPair` constructor.
- `deriveFirst _ _ = [``{m}]`: We implement `deriveFirst` to return a list of arguments that must be generated first. Here, we specify the argument
named `m` using a name literal ```{m}`.

### Test It

With this instance in scope, `deriveGen` will now follow our instructions. When generating an `LtPair`, it will generate `m` first, and then be smart
enough to only generate values for `n` that are less than `m`.

```idris
-- A main function to test the LtPair generator
main_lt : IO ()
main_lt = do
  let reportTemplate = initCoverageInfo genLtPair
  let rawCoverageRuns = unGenTryND 1000 someStdGen (genLtPair (limit 10))
  let allRawCoverage = concatMap fst rawCoverageRuns
  let finalReport = registerCoverage allRawCoverage reportTemplate
  putStrLn $ show finalReport
```

You will see that this generator efficiently produces valid pairs like `MkLtPair 5 10 True` every time, without the wasteful failures of the naive
approach.

---

## Next Steps

- **Want to integrate handwritten generators?** Continue to **[Mixing Manual and Automatic Generation](t06-mixing-manual-and-automatic.md)** to see how
`deriveGen` automatically discovers and uses your custom generators.
- **Want to generate types with proof constraints?** Continue to **[Generating GADTs with Proofs](t08-generating-gadts-with-proofs.md)** to see how
`deriveGen` handles GADTs with auto-implicit proof arguments.
- **Want to see a complete example?** Continue to **[Toy Example: Generating ASTs for a DSL](t09-toy-example.md)** to build a complete generator for a
simple imperative language.
