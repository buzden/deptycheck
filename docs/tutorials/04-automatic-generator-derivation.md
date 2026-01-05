# 4. Automatic Generator Derivation

In the previous tutorials, we showed how to write generators by hand. This is fine for simple types, but quickly becomes tedious and error-prone for complex, recursive data structures.

This is where `DepTyCheck` shines. It comes with a powerful macro, `deriveGen`, that inspects your data type at compile-time and automatically writes a high-quality generator for it, handling recursion and constraints for you.

### Our Goal

In this tutorial, we will use a single, running example—a file system `Entry`—to demonstrate the power of `deriveGen`. We will:

1.  Show how complex a manual generator for `Entry` would be.
2.  Replace it with a single `deriveGen` call.
3.  Learn how to provide an **external generator** to produce meaningful filenames.
4.  Learn how to **pass arguments** to the generator to make it context-aware.

### Prerequisites

-   Completion of the tutorials on [manual generation](01-generator-monad.md), [emptiness](02-handling-emptiness.md), and [coverage analysis](03-measuring-test-coverage.md).

---

## Step 1: The Burden of Manual Derivation

Let's start with a recursive data type for a file system entry.

```idris
data Entry = File String | Directory (List Entry)
```

How would we write a generator for this by hand? It would be complex:
- We would need to accept a `Fuel` parameter to stop recursion.
- In the `Directory` case, we'd need to call ourself with less fuel.
- We'd have to balance the choice between `File` and `Directory` to get a good distribution.
- We would need a separate generator for the `String` in `File`.

A sketch might look like this (don't type this):
```idris
-- A complex, manual generator (conceptual)
genEntryManual : Fuel -> Gen MaybeEmpty Entry
genEntryManual Dry = pure (File "default.txt") -- Base case when out of fuel
genEntryManual (More recFuel) =
  frequency
    [ (1, [| File ... |]) -- some string generator
    , (1, [| Directory (listOf recFuel (genEntryManual recFuel)) |]) -- recursive call
    ]
```
This is a lot of work to get right. Now, let's do it the easy way.

---

## Step 2: Automatic Derivation with `deriveGen`

We can replace all of that manual logic with a single line.

1.  **Create a new file** named `DeriveTutorial.idr`.

2.  **Add the necessary setup.** We need the `%language ElabReflection` pragma to enable compile-time macros, and the correct imports.

    ```idris
    %language ElabReflection

    module DeriveTutorial

    import Deriving.DepTyCheck.Gen -- For the deriveGen macro
    import Data.Fuel

    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Runner
    import System.Random.Pure.StdGen

    data Entry = File String | Directory (List Entry)
    ```

3.  **Define the generator.** That's it. The `deriveGen` macro will now inspect the `Entry` type and write a generator that handles recursion, fuel, choices, and even includes a default generator for `String`. It also automatically adds the coverage labels we learned about in the last tutorial!

    ```idris
    genEntryDefault : Fuel -> Gen MaybeEmpty Entry
    genEntryDefault = deriveGen
    ```

4.  **Test It!** You can immediately generate a random file system structure.
    ```idris
    main : IO ()
    main = do
      Just e <- pick1 (genEntryDefault (limit 10))
        | Nothing => printLn "Generation failed"
      printLn e
    ```
    Running this might produce output like: `Directory [File "a", Directory [File "b"]]`.

---

## Step 3: Providing an External Generator

The default generator is powerful, but the `String`s it produces are random nonsense. To generate meaningful data, we can provide `deriveGen` with a "hint" in the form of an external generator.

1.  **Write a custom `String` generator.** This generator will produce realistic filenames.

    ```idris
    genFilename : Fuel -> Gen MaybeEmpty String
    genFilename _ = elements ["config.yml", "main.idr", "README.md"]
    ```

2.  **Modify the generator signature.** To tell `deriveGen` to use our custom generator, we add it as a constraint to the signature. This is `deriveGen`'s way of asking for help: "When you need a `String`, you must provide me with a generator for it."

    ```idris
    genEntryWithHint : (Fuel -> Gen MaybeEmpty String) => Fuel -> Gen MaybeEmpty Entry
    genEntryWithHint = deriveGen
    ```

3.  **Call the new generator.** When we call `genEntryWithHint`, we now use the `@{...}` syntax to pass our `genFilename` function to satisfy the constraint.

    ```idris
    main_hint : IO ()
    main_hint = do
      putStrLn "--- Generating Entries with a custom String generator ---"
      replicate 5 $ do
        Just e <- pick1 (genEntryWithHint @{genFilename} (limit 5))
          | Nothing => printLn "Generation failed"
        printLn e
    ```

4.  **Analyze the output.** You will see that `deriveGen` still handles the `Directory` and `List` logic automatically, but every `File` now contains one of your hand-picked filenames.

    ```
    --- Generating Entries with a custom String generator ---
    Directory [File "main.idr"]
    File "config.yml"
    Directory []
    File "README.md"
    Directory [Directory [File "config.yml"]]
    ```

---

## Step 4: Passing Runtime Arguments

Sometimes, a generator needs more context than `Fuel`. For example, what if we want to generate files with names that are context-dependent, based on their parent directory?

Any arguments that appear in the signature *before* the `Fuel` parameter are treated as regular inputs. `deriveGen` is smart enough to thread these arguments through its recursive calls.

1.  **Write a context-aware `String` generator.** This generator takes a `path` prefix as an argument and changes its output accordingly.

    ```idris
    genContextAwareFilename : String -> Fuel -> Gen MaybeEmpty String
    genContextAwareFilename path _ =
        if path == "src"
           then elements ["main.idr", "lib.idr"]
           else if path == "doc"
           then elements ["tutorial.md", "README.md"]
           else elements ["file.txt"]
    ```

2.  **Define a generator that accepts the `path` argument.** The `path : String` argument comes before `Fuel`. `deriveGen` now knows that when it needs a `String`, it should look for a generator of type `String -> Fuel -> Gen MaybeEmpty String` in the context.

    ```idris
    data CtxEntry = CtxFile String | CtxDir String (List CtxEntry)

    genCtxEntry : (path : String) -> (String -> Fuel -> Gen MaybeEmpty String) => Fuel -> Gen MaybeEmpty CtxEntry
    genCtxEntry path = deriveGen
    ```

3.  **Test it!** To call `genCtxEntry`, we provide the initial path, and our context-aware generator. The `deriveGen` engine will handle passing the `path` argument down to `genContextAwareFilename` during any recursive calls.

    ```idris
    main_args : IO ()
    main_args = do
      putStrLn "--- Generating files in `src` directory ---"
      -- We pass the initial path "src" and the context-aware generator
      let srcGen = genCtxEntry "src" @{genContextAwareFilename}
      Just e <- pick1 (srcGen (limit 4))
        | Nothing => printLn "Generation Failed"
      printLn e
    ```

4.  **Analyze the output.** You will see that files generated have names appropriate for the `src` directory, because our custom generator was called with `path = "src"`.

    ```
    --- Generating files in `src` directory ---
    CtxDir "src" [CtxFile "lib.idr", CtxFile "main.idr"]
    ```
This powerful pattern allows you to create highly flexible generators that adapt their behavior based on runtime context.

---

## Congratulations!

You have now unlocked the core power of `DepTyCheck`. You can say goodbye to writing boilerplate generators and let the compiler do the work for you, while still providing guidance when needed.

In this tutorial, you learned:

*   ✅ How to replace a complex, manual recursive generator with a single `deriveGen` macro.
*   ✅ How to provide a **custom generator** for a base type like `String` by adding a `=>` constraint to the signature.
*   ✅ How to pass **runtime arguments** to a derived generator to make it more flexible and context-aware.

### Next Steps

Now that you know how to automatically generate data and provide hints, you are ready for advanced topics.

*   **How do I fix a biased generator or control generation order?** The default derivation strategy is smart, but sometimes needs more specific guidance. Continue to **[Advanced Derivation Tuning](07-derivation-tuning.md)** to learn how to use `instance` declarations to control constructor probabilities and argument generation order.
