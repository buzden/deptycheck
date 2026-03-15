# 4. Automatic Generator Derivation

In the previous tutorials, we showed how to write generators by hand. This is fine for simple types, but quickly becomes tedious and error-prone for
complex, recursive data structures.

This is where `DepTyCheck` shines. It comes with a powerful macro, `deriveGen`, that inspects your data type at compile-time and automatically writes a
high-quality generator for it, handling recursion and constraints for you.

## Our Goal

In this tutorial, we will use a single, running example—a file system `Entry`—to demonstrate the power of `deriveGen`. We will:

1. Show how complex a manual generator for `Entry` would be.
2. Replace it with a single `deriveGen` call.
3. Learn how to provide an **external generator** to produce meaningful filenames.
4. Learn how to **pass arguments** to the generator to make it context-aware.

## Prerequisites

- Completion of [Installation and First Steps](t00-installation-and-setup.md) and the tutorials on [manual generation](t01-generator-monad.md),
[emptiness](t02-handling-emptiness.md), and [coverage analysis](t03-measuring-test-coverage.md).

### Create a new file named `DeriveTutorial.idr`

```idris
import Deriving.DepTyCheck.Gen -- For the deriveGen macro
import Data.Fuel

import Test.DepTyCheck.Gen
import System.Random.Pure.StdGen
```

We need the `%language ElabReflection` pragma to enable compile-time elaboration which will automatically write code for defined generators by their
types.

```idris
%language ElabReflection
```

---

## Step 1: The Burden of Manual Derivation

Let's start with a recursive data type for a file system entry.

```idris
data EntryManual = FileManual String | DirectoryManual (List EntryManual)

Show EntryManual where
  show (FileManual s) = "FileManual " ++ show s
  show (DirectoryManual l) = "DirectoryManual " ++ (assert_total $ show l)
```

How would we write a generator for this by hand? It would be complex:

- We would need to accept a `Fuel` parameter to stop recursion.
- In the `DirectoryManual` case, we'd need to call ourself with less fuel.
- We'd have to balance the choice between `FileManual` and `DirectoryManual` to get a good distribution.
- We would need a separate generator for the `String` in `FileManual`.

A sketch might look like this:

```idris
-- A complex, manual generator (conceptual)
genEntryManual : Fuel -> Gen MaybeEmpty EntryManual
genEntryManual Dry = pure (FileManual "default.txt") -- Base case when out of fuel
genEntryManual (More recFuel) =
  frequency
    [ (1, FileManual <$> elements ["file1", "file2"]) -- some string generator
    , (1, DirectoryManual <$> (listOf (genEntryManual recFuel)) ) -- recursive call
    ]
  where
```

Prepare a test for it:

```idris
runEntryManual : IO ()
runEntryManual = do
  printLn "limit = 1"
  for_ (the (List Int) [1..5]) $ \_ => do
    Just e <- pick (genEntryManual (limit 1))
      | Nothing => printLn "Generation failed"
    printLn e

  printLn "limit = 2"
  for_ (the (List Int) [1..5]) $ \_ => do
    Just e <- pick (genEntryManual (limit 2))
      | Nothing => printLn "Generation failed"
    printLn e

  printLn "limit = 3"
  for_ (the (List Int) [1..5]) $ \_ => do
    Just e <- pick (genEntryManual (limit 3))
      | Nothing => printLn "Generation failed"
    printLn e
```

This is a lot of work to get right. Now, let's do it the easy way.

---

## Step 2: Automatic Derivation with `deriveGen`

We can replace the manual logic with a single line. But it has some limitations. To make the automagic generation works we need to drop off polymorphic
parameters:

```idris
mutual
  data EntryList : Type where
    Nil : EntryList
    (::) : Entry -> EntryList -> EntryList

  data Entry = File String | Directory EntryList

mutual
  Show Entry where
    show (File s) = "File " ++ show s
    show (Directory l) = "Directory " ++ (assert_total $ show l)

  Show EntryList where
    show xs = "[" ++ show' xs ++ "]" where
      show' : EntryList -> String
      show' Nil        = ""
      show' (x :: Nil) = show x
      show' (x :: xs)  = show x ++ ", " ++ show' xs
```

```{note}
The latest version of DepTyCheck supports polymorphic specialization for automatically derived generators, but its support is still experimental. Also
automagic generator deriving supports only `Gen MaybeEmpty` for now. If you need stricter `Gen NonEmpty`, you still need to do it by your hands.
```

### Define the generator

Our first naive attempt to use `deriveGen` might be the following:

```idris
failing "No constructors found for the type `^prim^.String`"
  genEntry : Fuel -> Gen MaybeEmpty Entry
  genEntry = deriveGen
```

But honestly DepTyCheck is would decline our example because we need also to pass a generator for strings. It does not present out of the box, so, we
need some to add some special stuff around which will be uncovered by further tutorials.

```idris
%hint
genStr : Gen MaybeEmpty String
genStr = elements ["a", "b", "c", "d", "f", "g", "h"]

genEntry : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty Entry
genEntry = deriveGen
```

That's it. The `deriveGen` macro will now inspect the `Entry` type and write a generator that handles recursion, fuel, choices, and even attaches a
generator for `String` from the context. It might also automatically add the coverage labels we learned about in further tutorials!

You can immediately generate a random file system structure.

Prepare a test for it:

```idris
runEntryDefault : IO ()
runEntryDefault = do
  Just e <- pick (genEntry (limit 10))
    | Nothing => printLn "Generation failed"
  printLn e
```

Running this might produce output like: `Directory [File "a", Directory [File "b"]]`.

---

## Step 3: Providing an External Generator

The default generator is powerful, but the `String`s it produces are random nonsense. To generate meaningful data, we can provide `deriveGen` with a
"hint" in the form of an external generator.

### Write a custom `String` generator

This generator will produce realistic filenames.

```idris
genFilename : Fuel -> Gen MaybeEmpty String
genFilename _ = elements ["config.yml", "main.idr", "README.md"]
```

### Call the new generator

When we call `genEntry`, we can use the `@{...}` syntax to pass our `genFilename` function to satisfy the constraint.

```idris
runEntryWithHint : IO ()
runEntryWithHint = do
  putStrLn "--- Generating Entries with a custom String generator ---"
  for_ (the (List Int) [1..5]) $ \_ => do
    Just e <- pick (genEntry @{genFilename} (limit 5))
      | Nothing => printLn "Generation failed"
    printLn e
```

You will see that `deriveGen` still handles the `Directory` and `List` logic automatically, but every `File` now contains one of your hand-picked
filenames.

```text
--- Generating Entries with a custom String generator ---
Directory [File "main.idr"]
File "config.yml"
Directory []
File "README.md"
Directory [Directory [File "config.yml"]]
```

---

## Step 4: Passing Runtime Arguments

Sometimes, a generator needs more context than `Fuel`. For example, what if we want to generate files with names that are context-dependent, based on
their parent directory?

Any arguments that appear in the signature _before_ the `Fuel` parameter are treated as regular inputs. `deriveGen` is smart enough to thread these
arguments through its recursive calls.

### Write a context-aware `String` generator

This generator takes a `path` prefix as an argument and changes its output accordingly.

```idris
genContextAwareFilename : String -> Fuel -> Gen MaybeEmpty String
genContextAwareFilename path _ =
  if path == "src"
      then elements ["main.idr", "lib.idr"]
      else if path == "doc"
      then elements ["tutorial.md", "README.md"]
      else elements ["file.txt"]
```

To call `genCtxEntry`, we provide the initial path, and our context-aware generator. The `deriveGen` engine will handle passing the `path` argument down
to `genContextAwareFilename` during any recursive calls.

Prepare a test for it:

```idris
runCtxEntry : IO ()
runCtxEntry = do
  putStrLn "--- Generating files in `src` directory ---"
  -- We pass the initial path "src" and the context-aware generator
  Just e <- pick (genEntry @{genContextAwareFilename "src"} (limit 5))
    | Nothing => printLn "Generation Failed"
  printLn e
```

You will see that files generated have names appropriate for the `src` directory, because our custom generator was called with `path = "src"`.

```text
--- Generating files in `src` directory ---
Directory [Directory [], Directory [], File "main.idr", File "lib.idr"]
```

This powerful pattern allows you to create highly flexible generators that adapt their behavior based on runtime context.

---

## Next Steps

Now that you know how to automatically generate data and provide hints, you are ready for more advanced topics:

- **Want to learn how to control what gets generated?** Continue to **[DeriveGen Signatures](t05-derivegen-signatures.md)** to learn how to use given vs
generated parameters and dependent pairs in signatures.
- **Want to understand how recursion affects generation?** Continue to **[Beyond Fuel](t07-beyond-fuel.md)** to learn about `SpendingFuel` vs
`StructurallyDecreasing` recursion.
- **How do I fix a biased generator or control generation order?** The default derivation strategy is smart, but sometimes needs more specific guidance.
Continue to **[Derivation Tuning](t10-derivation-tuning.md)** to learn how to use `instance` declarations to control constructor probabilities and
argument generation order.
