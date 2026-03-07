# 3. Measuring Your Test Coverage

In the last tutorials, we learned how to write generators for random data. But how do we know if our random data is _good_? Are we testing all the important cases, or is our generator accidentally biased, leaving critical parts of our code untested?

If a generator only ever produces one kind of value, our tests won't find bugs that only appear in other cases. We need a way to measure the quality of our random data.

## Our Goal

In this tutorial, you will learn how to add **labels** to your generators to measure your test coverage. You will build a generator for a `TrafficLight` data type, add labels to track each color, and run a test that produces a coverage report, like this:

```text
TrafficLight covered fully (1000 times)
  - Red: covered (332 times)
  - Green: covered (334 times)
  - Amber: covered (334 times)
```

## Prerequisites

This tutorial assumes you have completed [Installation and First Steps](t00-installation-and-setup.md) and the first two tutorials on [basic generation](t01-generator-monad.md) and [emptiness handling](t02-handling-emptiness.md).

---

## Step 1: Creating a Generator to Test

First, let's create a simple data type and a generator for it. This will be the subject of our coverage analysis.

### Create a new file named `CoverageTutorial.idr`

```idris
import Data.List
import Data.List.Lazy
import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Coverage
import System.Random.Pure.StdGen

import Control.Monad.Maybe
import Control.Monad.Random
import Control.Monad.State
```

### Add the following code to it

```idris
data TrafficLight = Red | Amber | Green

Show TrafficLight where
  show Red = "Red"
  show Amber = "Amber"
  show Green = "Green"

-- A generator that produces a traffic light color
genTrafficLight : Gen1 TrafficLight
genTrafficLight = oneOf [pure Red, pure Amber, pure Green]
```

This generator works, but we have no way of knowing if it's distributing its results evenly. To see that, we need to add labels.

---

## Step 2: Generating the Coverage Report

To get a full, aggregated coverage report, we need to run the generator many times and combine the results. This is a three-step process:

1. Initialize Report: Create an empty `CoverageGenInfo` report. This serves as a template that knows about all the types and constructors in our generator.
2. Collect Data: Run the generator many times and collect the raw `ModelCoverage` (the label counts) from each individual run.
3. Analyze Results: Fold the collected raw data into the report template to produce the final, printable `CoverageGenInfo`.

> [!NOTE]\
> Coverage measurement happens in three phases:
>
> 1. Generate many samples with different random seeds
> 2. Track which constructors appear
> 3. Report how much every constructor had been called

Here is how to implement this in a `main` function.

### Add a `main` function to your `CoverageTutorial.idr` file

```idris
runReportWithCoverage : IO ()
runReportWithCoverage = do
  -- Step 1: Initialize the report template.
  let reportTemplate = initCoverageInfo genTrafficLight

  -- Step 2: Run the generator 1000 times to collect raw coverage data.
  -- `withCoverage` is needed here because our generator is written by hand.
  let rawCoverageRuns = unGenTryND 1000 someStdGen (withCoverage genTrafficLight)
  let allRawCoverage = concatMap fst rawCoverageRuns

  -- Step 3: Fold the raw data into the template to get the final report.
  let finalReport = registerCoverage allRawCoverage reportTemplate

  -- 4. Print the final report.
  putStrLn $ show finalReport
```

### Compile and run your file

```bash
idris2 --build CoverageTutorial.idr
./build/exec/CoverageTutorial
```

### Check the output

You will see the aggregated coverage report printed to your console. Because we used `oneOf`, the distribution should be very even:

```text
TrafficLight covered fully (1000 times)
  - Red: covered (332 times)
  - Green: covered (334 times)
  - Amber: covered (334 times)
```

This gives us high confidence that our generator is testing all three `TrafficLight` cases equally.

---

## Step 3: Debugging with Labels

Besides aggregated reports, labels are also an invaluable tool for debugging. You can instruct the generator runner to print every label as it's activated. This allows you to trace the execution of a single, complex generation.

`DepTyCheck` uses the `CanManageLabels` interface to handle this. By default, the `pick` function we've used before uses the `IgnoreLabels` implementation. But we can provide a different one, `PrintAllLabels`, to change its behavior.

### Add a new `runDebug` function to your file

This new function will use `pick` and provide the `PrintAllLabels` implementation via the `@{}` syntax.

```idris
runDebug : IO ()
runDebug = do
  Just v <- runMaybeT {m=IO}
    $ evalRandomT someStdGen
    $ evalStateT Z $ unGen {labels = PrintAllLabels} (withCoverage genTrafficLight)
    | Nothing => putStrLn "couldn't produce a value"
  putStrLn $ "Generated withCoverage: " ++ show v

  val <- pick genTrafficLight
  putStrLn $ "Generated via pick: " ++ show val
```

### Compile and run the file again

```bash
    idris2 --build CoverageTutorial.idr
    ./build/exec/CoverageTutorial
```

### Analyze the output. You will see a clear difference

```text
Main.TrafficLight[?]
Main.Amber (user-defined)
Generated withCoverage: Amber
Generated via pick: Just Green
```

In the first run, the label was printed to the console the moment the corresponding generator was executed. In second run, no label were printed. For a deeply nested generator, this trace allows you to understand exactly which path was taken to produce a specific problematic value.

---

## Next Steps

Now that you can write, run, and measure generators manually, it's time to learn how `DepTyCheck` can do all of this for you automatically.

- **Next Tutorial:** Continue to **[Automatic Generator Derivation](t04-automatic-generator-derivation.md)** to learn how to use `deriveGen`.
