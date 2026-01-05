# 7. Advanced Derivation Tuning

In the last tutorial, we saw how to use `deriveGen` and provide it with custom generators for base types like `String`. However, `DepTyCheck` offers even deeper, more powerful mechanisms for controlling the derivation process for situations where just providing a generator isn't enough.

> **Disclaimer: This is an Advanced Tutorial.** The tuning mechanism uses some of Idris's more powerful features, specifically compile-time reflection and type class instances. We will walk through it step-by-step, but a full explanation of these concepts is beyond the scope of this tutorial. If you just want to use `deriveGen` with its default settings and provide external generators, you can safely skip this lesson.

### Our Goal

We will tackle two common problems that cannot be solved with external generators alone:

1.  **Fixing Bias:** We will prove that a default generator is biased and then implement the `ProbabilityTuning` interface to change the frequency of a specific constructor.
2.  **Fixing Inefficiency:** We will show how a naive generator for a constrained type is inefficient and then implement the `GenOrderTuning` interface to guide the derivation logic and make it robust.

### Prerequisites

-   Completion of [Automatic Generator Derivation](04-automatic-generator-derivation.md).
-   A willingness to engage with some advanced Idris concepts!

---

## Step 1: Discovering a Biased Generator

Let's start by defining a simple, recursive data type where the default `deriveGen` strategy will produce a biased result.

1.  **Create a new file** named `TuningTutorial.idr`.

2.  **Add the following code.**

    ```idris
    %language ElabReflection

    module TuningTutorial

    import Deriving.DepTyCheck.Gen
    import Deriving.DepTyCheck.Gen.Tuning -- For the tuning interfaces
    import Data.Fuel
    import public Data.So

    -- From previous tutorials
    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Gen.Coverage
    import Test.DepTyCheck.Runner
    import System.Random.Pure.StdGen

    data Entry = File String | Directory (List Entry)

    -- A generator for Entry that takes an external String generator
    genEntry : (Fuel -> Gen MaybeEmpty String) => Fuel -> Gen MaybeEmpty Entry
    genEntry = deriveGen
    ```

3.  **Add a simple `String` generator** and the coverage analysis `main` function.

    ```idris
    genAnyString : Fuel -> Gen MaybeEmpty String
    genAnyString _ = elements ["a", "b", "c"]

    main : IO ()
    main = do
      let reportTemplate = initCoverageInfo (genEntry @{genAnyString})
      let rawCoverageRuns = unGenTryND 1000 someStdGen (genEntry @{genAnyString} (limit 10))
      let allRawCoverage = concatMap fst rawCoverageRuns
      let finalReport = registerCoverage allRawCoverage reportTemplate
      putStrLn $ show finalReport
    ```

4.  **Analyze the report.** The results will be starkly imbalanced because `deriveGen` prefers the non-recursive `File` constructor.

    ```
    Entry covered fully (1000 times)
      - File: covered (909 times)
      - Directory: covered (91 times)
    ```
    This is the problem we need to solve.

---

## Step 2: Probability Tuning with an `instance`

To fix the bias, we must implement the `ProbabilityTuning` interface for the `Directory` constructor. This tells `deriveGen` to override its default weight.

1.  **Define the `instance`.** Place this `instance` declaration at the top level of your file. It targets the `Directory` constructor by its full name.

    ```idris
    instance ProbabilityTuning "TuningTutorial.Directory".dataCon where
      isConstructor = itIsConstructor
      tuneWeight _ = 10
    ```
    - `instance ProbabilityTuning ... where`: We are defining a specific implementation of this interface.
    - `"TuningTutorial.Directory".dataCon`: This is a `Name` literal that refers to the `Directory` constructor inside the `TuningTutorial` module.
    - `isConstructor = itIsConstructor`: This is a required line of reflection boilerplate that confirms we have targeted a valid constructor.
    - `tuneWeight _ = 10`: We implement the `tuneWeight` function. It takes the default weight `_` and we ignore it, always returning our new, higher weight of `10`.

2.  **Re-run the coverage analysis.** The `deriveGen` call in `genEntry` does not change. The compiler will now automatically find and apply our `instance`. Simply recompile and run.

3.  **Analyze the new report.** The distribution will now be much closer to a 50/50 balance, proving we have successfully tuned the probability.

    ```
    Entry covered fully (1000 times)
      - File: covered (526 times)
      - Directory: covered (474 times)
    ```

---

## Step 3: Generation Order Tuning with an `instance`

Probability isn't the only thing we can tune. For some dependent types, the *order* in which arguments are generated is critical for efficiency. Consider a pair `(n, m)` where we require `n < m`.

```idris
data LtPair : Type where
  MkLtPair : (n : Nat) -> (m : Nat) -> (prf : So (n < m)) -> LtPair
```

`deriveGen`'s default strategy might randomly pick `n=10` and `m=5`, then fail because it can't prove `10 < 5`. This is very inefficient. We can tell it to generate `m` first, making it much easier to pick a valid `n`.

1.  **Define the generator and the tuning `instance`** in your `TuningTutorial.idr` file.

    ```idris
    genLtPair : Fuel -> Gen MaybeEmpty LtPair
    genLtPair = deriveGen

    instance GenOrderTuning "TuningTutorial.MkLtPair".dataCon where
      isConstructor = itIsConstructor
      deriveFirst _ _ = [`{m}]
    ```
    - `GenOrderTuning ... where`: We implement the ordering interface for the `MkLtPair` constructor.
    - `deriveFirst _ _ = [`{m}]`: We implement `deriveFirst` to return a list of arguments that must be generated first. Here, we specify the argument named `m` using a name literal `` `{m}``.

2.  **Test It.** With this instance in scope, `deriveGen` will now follow our instructions. When generating an `LtPair`, it will generate `m` first, and then be smart enough to only generate values for `n` that are less than `m`.

    ```idris
    -- A main function to test the LtPair generator
    main_lt : IO ()
    main_lt = do
      putStrLn "--- Generating 5 pairs where n < m ---"
      replicate 5 $ do
        Just p <- pick1 (genLtPair (limit 10))
          | Nothing => printLn "Generation failed"
        printLn p
    ```
    You will see that this generator efficiently produces valid pairs like `MkLtPair 5 10 True` every time, without the wasteful failures of the naive approach.

---

## Congratulations!

You have now learned the true, advanced methods for controlling `DepTyCheck`'s derivation engine. By implementing the tuning interfaces, you can provide expert guidance to the compiler, resulting in efficient and well-distributed test data for any data type.

In this tutorial, you learned how to:

*   ✅ **Prove Bias:** Use coverage analysis to find and prove when a default generator is not producing a good data distribution.
*   ✅ **Tune Probabilities:** Implement the `ProbabilityTuning` interface to fix biases by giving a constructor a new `Weight`.
*   ✅ **Tune Generation Order:** Implement the `GenOrderTuning` interface to tell `deriveGen` which arguments to generate first, making generation for constrained dependent types more efficient.
*   ✅ Use advanced Idris features like `instance` declarations and `Name` literals to apply these tuning rules.

This completes the core `DepTyCheck` tutorial series! You now have the full range of skills, from simple manual generation to full directorial control over the powerful automatic derivation engine. To better understand how `deriveGen` works, continue to the next tutorial, **[Under the Hood: Building a `deriveGen`-like Macro](08-under-the-hood-a-derivegen-like-macro.md)**.
