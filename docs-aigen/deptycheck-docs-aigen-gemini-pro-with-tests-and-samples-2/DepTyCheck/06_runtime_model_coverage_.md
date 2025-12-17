# Chapter 6: Runtime Model Coverage

In the last chapter, [Example: Primitive Imperative Languages (PIL)](05_example__primitive_imperative_languages__pil__.md), we saw how `DepTyCheck` can generate incredibly complex things, like entire type-safe programs. These programs are guaranteed to be *correct* according to the type system. But is our *generator* itself any good?

How do we know we're not just generating the same simple program over and over again? How can we be sure our random test data is actually diverse enough to find interesting bugs?

This chapter introduces **Runtime Model Coverage**, a powerful quality control tool for your generators. It acts like an inspector, watching what your generator produces and giving you a detailed report.

## The Problem: Are We Testing Everything?

Imagine you're the head chef of a restaurant. You've created a "Random Dish of the Day" recipe (`Gen Dish`). After a week, you want to know if you've been offering a good variety. Did you use all the main ingredients you have (chicken, beef, tofu)? Or did you accidentally make chicken every single day?

This is a common problem in testing. Our generators might have "blind spots"—parts of our data types that they never, or rarely, produce.

Let's use a simple data type for a traffic light:

```idris
data Light = Red | Amber | Green
```

We can easily derive a generator for it.

```idris
import Deriving.DepTyCheck.Gen

genLight : Fuel -> Gen Light
genLight = deriveGen
```

If we run this generator 100 times, we'd hope to see a good mix of `Red`, `Amber`, and `Green`. But what if, due to a bug or some complex [Derivation Strategy Tuning](04_derivation_strategy_tuning_.md), our generator only ever produced `Red`? Our tests would have a massive blind spot: we'd never be testing the `Amber` or `Green` cases! We need a way to check this.

## The Solution: `withCoverage` and Friends

`DepTyCheck` provides a simple way to get a summary report of what your generator has been creating. It involves three simple steps:

1.  **Wrap** your generator with `withCoverage`.
2.  **Generate** values and collect coverage data.
3.  **Display** a summary report.

### Step 1: Wrap Your Generator with `withCoverage`

`withCoverage` is a special tool that you wrap around an existing generator. It doesn't change the values the generator produces, but it attaches a "tag" to each one, indicating which constructor was used to create it.

```idris
import Test.DepTyCheck.Gen.Coverage

-- Same generator as before, but now with coverage tracking.
genLightWithCoverage : Fuel -> Gen Light
genLightWithCoverage = withCoverage genLight
```

Think of this as putting a little sticker on each dish that leaves the kitchen: "Made with Chicken", "Made with Beef", etc. The dish is the same, but now it has a label for our report.

### Step 2: Generate Values and Collect Data

Now we need a loop that runs our generator many times and collects all the "stickers" into a report.

First, we create an empty report template using `initCoverageInfo`. This looks at our `Light` type and prepares a checklist for all its constructors: `Red`, `Amber`, and `Green`.

```idris
lightCoverage : CoverageGenInfo genLight
lightCoverage = initCoverageInfo {x=genLight}
```
Next, we'll write a small IO action that runs the generator, gets the value and its "sticker" (the coverage data), and adds it to our report.

`unGenD'` is the function we use to run a generator and get its coverage data. It returns the generated value *and* the `ModelCoverage` for that single run. We then use `registerCoverage` to add this to our main report.

```idris
-- Generate one value and update the report
generateOne : CoverageGenInfo g -> IO (CoverageGenInfo g)
generateOne info = do
  -- Run the generator to get a value and its coverage data
  Just (coverage, val) <- unGenD' (genLightWithCoverage (limit 10))
    | Nothing => pure info -- If generation fails, do nothing

  -- Add this run's coverage to our main report
  pure (registerCoverage coverage info)
```

### Step 3: Display the Report

Finally, we can loop our `generateOne` function 100 times and print the final report.

```idris
main : IO ()
main = do
  -- Start with an empty report
  let initialReport = initCoverageInfo {x=genLight}

  -- Run the generator 100 times, updating the report each time
  finalReport <- foldl (\acc, => acc >>= generateOne) (pure initialReport) (replicate 100 ())

  -- Print the final summary!
  print finalReport
```

When you run this, you'll see a beautiful, colourful summary right in your terminal:

```ansi
[1m[34mMain.Light[0m [1m[32mcovered fully[0m (100 times)
  - [2mpath/to/your/file.idr:3:1[0m: [1m[32mcovered[0m (33 times)
  - [2mpath/to/your/file.idr:3:7[0m: [1m[32mcovered[0m (35 times)
  - [2mpath/to/your/file.idr:3:15[0m: [1m[32mcovered[0m (32 times)
```

This report tells us:
*   The `Main.Light` type was "covered fully," meaning all of its constructors were used.
*   The generator was run 100 times in total.
*   Each constructor (located at line 3, columns 1, 7, and 15) was used about a third of the time.

If `Green` had never been generated, its line would be bright red and say "**not covered**", instantly showing you the blind spot in your test data!

## How It Works: Under the Hood

The magic of `withCoverage` is a combination of compile-time code generation and a classic programming pattern called the `Writer` monad.

### The `withCoverage` Macro

When the compiler sees `withCoverage gen`, it doesn't just run `gen`. It's a macro that *rewrites* your generator at compile time.

```mermaid
sequenceDiagram
    participant User
    participant Compiler
    participant withCoverage as withCoverage macro
    participant TypeInfo as `Light` Type Definition

    User->>Compiler: Compiles `withCoverage genLight`
    Compiler->>withCoverage: Please expand this macro
    withCoverage->>TypeInfo: What is the return type of `genLight`?
    TypeInfo-->>withCoverage: It's `Light`
    withCoverage->>TypeInfo: What are the constructors of `Light`?
    TypeInfo-->>withCoverage: `Red`, `Amber`, and `Green`
    withCoverage->>withCoverage: I will write new code...
    Note over withCoverage: The new code will run `genLight`,<br/> then `case` match on the result<br/> to find the constructor name.
    withCoverage->>Compiler: Here is the rewritten generator code
end
```

The rewritten code looks something like this (in spirit):

```idris
-- This is what `withCoverage` generates for you
\fuel => do
  -- 1. Run the original generator
  val <- genLight fuel

  -- 2. Figure out which constructor was used
  let theLabel = case val of
                   Red   => "Red"
                   Amber => "Amber"
                   Green => "Green"

  -- 3. Attach the label and return the original value
  label (fromString theLabel) (pure val)
```
This new generator does exactly what the old one did, but it has an extra step to `label` the result before returning it.

### `label`, `unGenD'`, and the `Writer` Monad

So what does `label` do? It's a helper function that uses a `Writer` monad. You can think of a `Writer` monad as a computation that carries a little logbook with it.

*   The `label` function (defined in `Test.DepTyCheck.Gen.Labels`) simply writes a new entry into this "logbook".
*   The `unGenD'` function (from `Test.DepTyCheck.Gen.Coverage`) is a special version of the generator runner. After the generator finishes, `unGenD'` uses `runWriterT` to open the logbook, collect all the entries, and return them to you as `ModelCoverage`.

This is why `unGenD'` returns a pair: `(ModelCoverage, a)`. It's the collected logbook and the final value. The `registerCoverage` function then simply reads this logbook and updates the master report's counters.

## Conclusion

You've now learned how to become a quality inspector for your own test data generators. Runtime Model Coverage is an essential debugging tool that gives you confidence in your testing process.

-   **`withCoverage`** is a macro that "tags" values from a generator with the name of the constructor used to create them.
-   **`initCoverageInfo`** creates an empty report card for your type's constructors.
-   **`unGenD'`** runs a generator and returns both the value and its "tag".
-   **`registerCoverage`** updates the report card with the result of a single run.

By using these tools, you can ensure your automatically generated test data is diverse and covers all the interesting edge cases defined in your types, helping you find bugs that might otherwise have stayed hidden.

We have now explored the full suite of `DepTyCheck`'s user-facing features. What if you want to extend the library or build your own tools using its powerful foundation? In our final chapter, we'll take a look under the hood at the core machinery that makes it all possible.

Onward to [**Derivation Internals & Utilities**](07_derivation_internals___utilities_.md)

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)