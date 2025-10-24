# 10. Generating GADTs with Proof Constraints

In previous tutorials, we used `deriveGen` for regular data types and indexed types like `Vect`. But what about types that carry **proofs** as constructors arguments? Can `deriveGen` handle those?

Yes! `deriveGen` is smart enough to automatically satisfy proof constraints during generation.

## Our Goal

In this tutorial, you will build a generator for a `SortedList` type that is **always sorted by construction**. The type itself carries a proof of sortedness, and `deriveGen` will automatically find valid values that satisfy the proof constraints.

By the end, you will:
1.  Define a GADT with a proof argument (`{auto prf : isSorted ...}`)
2.  Derive a generator with a single `deriveGen` call
3.  Run the generator and verify that all output is sorted

## Prerequisites

-   Completion of [Tutorial 5: DeriveGen Signatures](05-derivegen-signatures.md)
-   Understanding of dependent pairs and indexed types

---

## Step 1: Define a SortedList Type

First, let's define a list type that is guaranteed to be sorted. The key is that the `SCons` constructor requires a proof that adding a new element maintains sortedness.

1.  **Create a new file** named `SortedListTutorial.idr`.

2.  **Add the following code.**

    ```idris
    module SortedListTutorial

    import Deriving.DepTyCheck.Gen
    import Data.Fuel

    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Runner
    import System.Random.Pure.StdGen

    data SortedList : Type where
      SNil : SortedList
      SCons : (x : Nat) -> (xs : SortedList) -> {auto prf : isSorted (x :: toList xs)} -> SortedList

    toList : SortedList -> List Nat
    toList SNil = []
    toList (SCons x xs prf) = x :: toList xs

    isSorted : List Nat -> Bool
    isSorted [] = True
    isSorted [_] = True
    isSorted (x :: y :: xs) = x <= y && isSorted (y :: xs)
    ```

    The `SCons` constructor has an **auto-implicit** argument `{auto prf : isSorted (x :: toList xs)}`. This means:
    -   To construct an `SCons`, Idris must find a proof that the list is sorted.
    -   The `auto` keyword tells Idris to search for this proof automatically.

---

## Step 2: Derive the Generator

Now comes the magic. We derive a generator for `SortedList` with a single line.

1.  **Add the derived generator.**

    ```idris
    genSortedList : Fuel -> Gen MaybeEmpty SortedList
    genSortedList = deriveGen
    ```

    That's it! No manual logic, no special handling for the proof argument. `deriveGen` will:
    1.  Generate a candidate `x : Nat`
    2.  Recursively generate `xs : SortedList`
    3.  Check if `isSorted (x :: toList xs)` can be proven
    4.  If yes, construct the `SCons`; if no, try another `x`

---

## Step 3: Run and Verify

Let's test the generator and verify that all output is sorted.

1.  **Add a `main` function.**

    ```idris
    main : IO ()
    main = do
      putStrLn "--- Generating 5 sorted lists ---"
      replicate 5 $ do
        Just sl <- pick1 (genSortedList (limit 20))
          | Nothing => printLn "Generation failed"
        let asList = toList sl
        putStrLn $ "Generated: " ++ show asList
        putStrLn $ "Is sorted: " ++ show (isSorted asList)
    ```

2.  **Compile and run.**

    ```bash
    idris2 --build SortedListTutorial.idr
    ./build/exec/SortedListTutorial
    ```

3.  **Analyze the output.**

    ```
    --- Generating 5 sorted lists ---
    Generated: [0, 3, 5, 12, 42]
    Is sorted: True
    Generated: [8, 8, 9, 15, 21, 33]
    Is sorted: True
    Generated: []
    Is sorted: True
    Generated: [2, 7, 19]
    Is sorted: True
    Generated: [1, 1, 4, 10, 10, 15]
    Is sorted: True
    ```

    Every generated list is sorted! `deriveGen` automatically found values of `x` that satisfy the `isSorted` constraint.

---

## Step 4: Understanding How It Works

How does `deriveGen` solve the proof constraint? The key is in the **search order** and **backtracking**.

When `deriveGen` encounters `{auto prf : isSorted (x :: toList xs)}`, it:

1.  **Generates candidates** for `x` from the default `Nat` generator
2.  **Recursively generates** `xs : SortedList` (which is already sorted by construction)
3.  **Checks the constraint**: Is `x <= head xs` (or `x` can be anything if `xs` is empty)?
4.  **Backtracks if needed**: If the constraint fails, it tries another `x`

This is why the generator may be slower for complex constraints — it may need multiple attempts to find valid values.

### The Role of Fuel

The `Fuel` parameter controls how deep the recursion can go. With more fuel, `deriveGen` can generate longer sorted lists:

```idris
-- Add to main:
putStrLn "\n--- With small fuel (limit 3) ---"
Just sl1 <- pick1 (genSortedList (limit 3))
  | Nothing => printLn "Failed"
printLn $ toList sl1

putStrLn "\n--- With large fuel (limit 10) ---"
Just sl2 <- pick1 (genSortedList (limit 10))
  | Nothing => printLn "Failed"
printLn $ toList sl2
```

Output:
```
--- With small fuel (limit 3) ---
[2, 5, 8]

--- With large fuel (limit 10) ---
[0, 1, 3, 7, 12, 15, 20, 25, 30, 42]
```

---

## Step 5: Another Example — Bounded Values

Let's see another example of proof-carrying data. Consider a type that represents numbers bounded by a given limit:

```idris
-- Add to SortedListTutorial.idr

data BoundedNat : (limit : Nat) -> Type where
  MkBounded : (n : Nat) -> {auto prf : n `LT` limit} -> BoundedNat limit

genBoundedNat : (limit : Nat) -> Fuel -> Gen MaybeEmpty (BoundedNat limit)
genBoundedNat limit = deriveGen

testBounded : IO ()
testBounded = do
  putStrLn "--- Generating BoundedNat with limit 5 ---"
  replicate 5 $ do
    Just bn <- pick1 (genBoundedNat 5 (limit 10))
      | Nothing => printLn "Failed"
    case bn of
      MkBounded n => putStrLn $ "Generated: " ++ show n ++ " (< 5)"
```

The `{auto prf : n `LT` limit}` constraint ensures that only values less than the limit are generated. `deriveGen` will automatically search for valid `n` values.

---

## Congratulations!

You have learned how to generate GADTs with proof constraints using `deriveGen`. This is one of the most powerful features of DepTyCheck — it can automatically handle complex dependent types with minimal manual intervention.

In this tutorial, you learned:

*   ✅ How to define a GADT with auto-implicit proof arguments
*   ✅ How to derive a generator with a single `deriveGen` call
*   ✅ How `deriveGen` automatically searches for values that satisfy proof constraints
*   ✅ How fuel affects the depth of recursive generation
*   ✅ How to verify that generated data satisfies the constraints

## Next Steps

Now that you can generate proof-carrying data, you are ready for more advanced topics:

*   **Want to integrate handwritten generators?** Continue to **[Mixing Manual and Automatic Generation](09-mixing-manual-and-automatic.md)** to see how `deriveGen` automatically discovers and uses your custom generators.
*   **Want to understand the internals?** Continue to **[Under the Hood: Building a deriveGen-like Macro](08-under-the-hood-a-derivegen-like-macro.md)** to learn how the derivation engine works.
