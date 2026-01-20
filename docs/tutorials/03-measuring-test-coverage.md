# 3. Measuring Your Test Coverage

In the last tutorials, we learned how to write generators for random data. But how do we know if our random data is *good*? Are we testing all the important cases, or is our generator accidentally biased, leaving critical parts of our code untested?

If a generator only ever produces one kind of value, our tests won't find bugs that only appear in other cases. We need a way to measure the quality of our random data.

### Our Goal

In this tutorial, you will learn how to add **labels** to your generators to measure your test coverage. You will build a generator for a `TrafficLight` data type, add labels to track each color, and run a test that produces a coverage report, like this:

```
TrafficLight covered fully (1000 times)
  - Red: covered (332 times)
  - Green: covered (334 times)
  - Amber: covered (334 times)
```

### Prerequisites

This tutorial assumes you have completed the first two tutorials on [basic generation](01-generator-monad.md) and [emptiness handling](02-handling-emptiness.md).

---

## Step 1: Creating a Generator to Test

First, let's create a simple data type and a generator for it. This will be the subject of our coverage analysis.

1.  **Create a new file** named `CoverageTutorial.idr`.

2.  **Add the following code** to it.

    ```idris
    module CoverageTutorial

    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Gen.Coverage
    import Test.DepTyCheck.Runner
    import System.Random.Pure.StdGen

    data TrafficLight = Red | Amber | Green

    -- A generator that produces a traffic light color
    genTrafficLight : Gen1 TrafficLight
    genTrafficLight = oneOf [pure Red, pure Amber, pure Green]
    ```

This generator works, but we have no way of knowing if it's distributing its results evenly. To see that, we need to add labels.

---

## Step 2: Adding Labels to Track Coverage

The `label` function is the key to measuring coverage. It takes a `String` name and a generator and attaches a counter to that generation path.

1.  **Modify your `genTrafficLight` generator** to wrap each color's generator in a `label`.

    ```idris
    -- An instrumented generator that is now tracking coverage for each color.
    genTrafficLight : Gen1 TrafficLight
    genTrafficLight = oneOf
      [ label "Red"   (pure Red)
      , label "Amber" (pure Amber)
      , label "Green" (pure Green)
      ]
    ```

Now, every time this generator runs, it will record which of the three labeled paths was taken. In the next step, we'll see how to collect and display these recorded labels.

---

## Step 3: Generating the Coverage Report

To get a full, aggregated coverage report, we need to run the generator many times and combine the results. This is a three-step process:

1.  **Initialize Report:** Create an empty `CoverageGenInfo` report. This serves as a template that knows about all the types and constructors in our generator.
2.  **Collect Data:** Run the generator many times and collect the raw `ModelCoverage` (the label counts) from each individual run.
3.  **Analyze Results:** Fold the collected raw data into the report template to produce the final, printable `CoverageGenInfo`.

Here is how to implement this in a `main` function.

1.  **Add a `main` function** to your `CoverageTutorial.idr` file.

    ```idris
    main : IO ()
    main = do
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

2.  **Compile and run your file.**

    ```bash
    idris2 --build CoverageTutorial.idr
    ./build/exec/CoverageTutorial
    ```

3.  **Check the output.** You will see the aggregated coverage report printed to your console. Because we used `oneOf`, the distribution should be very even:

    ```
    TrafficLight covered fully (1000 times)
      - Red: covered (332 times)
      - Green: covered (334 times)
      - Amber: covered (334 times)
    ```

This gives us high confidence that our generator is testing all three `TrafficLight` cases equally.

---

## Step 4: Debugging with Labels

Besides aggregated reports, labels are also an invaluable tool for debugging. You can instruct the generator runner to print every label as it's activated. This allows you to trace the execution of a single, complex generation.

`DepTyCheck` uses the `CanManageLabels` interface to handle this. By default, the `pick1` function we've used before uses the `IgnoreLabels` implementation. But we can provide a different one, `PrintAllLabels`, to change its behavior.

1.  **Add a new `main_debug` function** to your file. This new `main` will use `pick1` and provide the `PrintAllLabels` implementation via the `@{}` syntax.

    ```idris
    main_debug : IO ()
    main_debug = do
      putStrLn "--- Running with PrintAllLabels ---"
      val <- pick1 genTrafficLight @{PrintAllLabels}
      putStrLn $ "Generated: " ++ show val

      putStrLn "\n--- Running with IgnoreLabels (the default) ---"
      val <- pick1 genTrafficLight
      putStrLn $ "Generated: " ++ show val
    ```

2.  **Compile and run the file again.**

    ```bash
    idris2 --build CoverageTutorial.idr
    ./build/exec/CoverageTutorial
    ```

3.  **Analyze the output.** You will see a clear difference:

    ```
    --- Running with PrintAllLabels ---
    Red
    Generated: Red

    --- Running with IgnoreLabels (the default) ---
    Generated: Amber
    ```
    In the first run, the label `"Red"` was printed to the console the moment the corresponding generator was executed. In the second run, no labels were printed. For a deeply nested generator, this trace allows you to understand exactly which path was taken to produce a specific problematic value.

## Congratulations!

You can now generate, analyze, and debug your test generators using labels.

In this tutorial, you learned how to:

*   ✅ Use `label` to instrument different paths in your generator.
*   ✅ **Aggregate Constructor Coverage:** Use `initCoverageInfo`, `unGenTryND`, and `registerCoverage` to produce a report on which constructors were hit.
*   ✅ **Debug Single Runs:** Use `PrintAllLabels` with `pick1` to trace the execution of a single generator run.
*   ✅ Understand that runners like `pick1` use a default `IgnoreLabels` implementation that can be overridden with the `@{...}` syntax.

### Next Steps

Now that you can write, run, and measure generators manually, it's time to learn how `DepTyCheck` can do all of this for you automatically.

*   **Next Tutorial:** Continue to **[Automatic Generator Derivation](./04-automatic-generator-derivation.md)** to learn how to use `deriveGen`.