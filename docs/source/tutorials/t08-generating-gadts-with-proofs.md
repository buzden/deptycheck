# 8. Generating GADTs with Proof Constraints

In previous tutorials, we used `deriveGen` for regular data types and indexed types like `Vect`. But what about types that carry **proofs** as
constructors arguments? Can `deriveGen` handle those?

Yes! `deriveGen` is smart enough to automatically satisfy proof constraints during generation.

## Our Goal

In this tutorial, you will build a generator for a `SortedList` type that is **always sorted by construction**. The type itself carries a proof of
sortedness, and `deriveGen` will automatically find valid values that satisfy the proof constraints.

By the end, you will:

1. Define a GADT with a proof argument (`{auto prf : isSorted ...}`)
2. Derive a generator with a single `deriveGen` call
3. Run the generator and verify that all output is sorted

## Prerequisites

- Completion of [Tutorial 5: DeriveGen Signatures](t05-derivegen-signatures.md)
- Understanding of dependent pairs and indexed types
- Idris2 source file `./src/Playground.idr` with the header:

```idris
import Deriving.DepTyCheck.Gen
import System.Random.Pure.StdGen
```

## Step 1: Define a SortedList Type

First, let's define a list type that is guaranteed to be sorted. The key is that the `SCons` constructor requires a proof that adding a new element
maintains sortedness.

```idris
isSorted : List Nat -> Bool
isSorted [] = True
isSorted [_] = True
isSorted (x :: y :: xs) = x <= y && isSorted (y :: xs)

mutual
  data SortedList : Type where
    SNil : SortedList
    SCons : (x : Nat) -> (xs : SortedList) -> {auto prf : So $ isSorted (x :: toList xs)} -> SortedList

  toList : SortedList -> List Nat
  toList SNil = []
  toList (SCons x xs) = x :: toList xs
```

The `SCons` constructor has an **auto-implicit** argument `{auto prf : isSorted (x :: toList xs)}`. This means:

- To construct an `SCons`, Idris must find a proof that the list is sorted.
- The `auto` keyword tells Idris to search for this proof automatically.

> [!NOTE]\
> The `{auto prf : isSorted ...}` constraint ensures only sorted lists are generated. The `auto` keyword makes Idris search for proof automatically
during generation.

---

## Step 2: Derive the Generator

Now comes the magic. We derive a generator for `SortedList` with a single line.

### Add the derived generator

```idris
genSortedList : Fuel -> Gen MaybeEmpty SortedList
genSortedList = deriveGen
```

That's it! No manual logic, no special handling for the proof argument. `deriveGen` will:

1. Generate a candidate `x : Nat`
2. Recursively generate `xs : SortedList`
3. Check if `isSorted (x :: toList xs)` can be proven
4. If yes, construct the `SCons`; if no, try another `x`

---

## Step 3: Run and Verify

Let's test the generator and verify that all output is sorted.

```idris
testList : HasIO io => io ()
testList = do
  putStrLn "--- Generating 5 sorted lists ---"
  for_ (the (List Int) [1..5]) $ \_ => do
    Just sl <- pick (genSortedList (limit 5))
      | Nothing => printLn "Generation failed"
    let asList = toList sl
    putStrLn $ "Generated: " ++ show asList
    putStrLn $ "Is sorted: " ++ show (isSorted asList)
```

### Compile and run

```bash
echo -e ':exec testList' | rlwrap pack repl ./src/Playground.idr
```

### Analyze the output

```text
...
Main> --- Generating 5 sorted lists ---
Generated: [2, 3, 3, 4, 4]
Is sorted: True
Generated: [2, 2]
Is sorted: True
Generated: [3, 4]
Is sorted: True
Generated: [2]
Is sorted: True
Generated: [4]
Is sorted: True
```

Every generated list is sorted! `deriveGen` automatically found values of `x` that satisfy the `isSorted` constraint.

---

## Step 4: Understanding How It Works

How does `deriveGen` solve the proof constraint? The key is in the **search order** and **backtracking**.

When `deriveGen` encounters `{auto prf : So $ isSorted (x :: toList xs)}`, it:

1. **Generates candidates** for `x` from the default `Nat` generator
2. **Recursively generates** `xs : SortedList` (which is already sorted by construction)
3. **Checks the constraint**: Is `x <= head xs` (or `x` can be anything if `xs` is empty)?
4. **Backtracks if needed**: If the constraint fails, it tries another `x`

> [!NOTE]\
> The proof argument guarantees sortedness by construction:
>
> - `SNil` is always sorted (base case)
> - `SCons` requires proof that new element maintains order
> - Invalid constructions are rejected at compile time

This is why the generator may be slower for complex constraints — it may need multiple attempts to find valid values.

The `Fuel` parameter controls how deep the recursion can go, so, with more fuel, `deriveGen` can generate longer sorted lists:

```idris
-- Add to main:
testFuel : IO ()
testFuel = do
  putStrLn "\n--- With small fuel (limit 3) ---"
  Just sl1 <- pick (genSortedList (limit 3))
    | Nothing => printLn "Generation failed"
  printLn $ toList sl1

  putStrLn "\n--- With large fuel (limit 8) ---"
  Just sl2 <- pick (genSortedList (limit 8))
    | Nothing => printLn "Generation failed"
  printLn $ toList sl2
```

Run it:

```bash
echo -e ':exec testFuel' | rlwrap pack repl ./src/Playground.idr
...
Main> --- Generating 5 sorted lists ---
Generated: [2, 3, 3, 4, 4]
Is sorted: True
Generated: [2, 2]
Is sorted: True
Generated: [3, 4]
Is sorted: True
Generated: [2]
Is sorted: True
Generated: [4]
Is sorted: True
```

---

## Step 5: Another Example — Bounded Values

Let's see another example of proof-carrying data. Consider a type that represents numbers bounded by a given limit:

```idris
data BoundedNat : (limit' : Nat) -> Type where
  MkBounded : (n : Nat) -> {auto prf : n `LT` limit'} -> BoundedNat limit'

genBoundedNat : Fuel -> (limit' : Nat) -> Gen MaybeEmpty (BoundedNat limit')
genBoundedNat = deriveGen

testBounded : IO ()
testBounded = do
  putStrLn "--- Generating BoundedNat with limit'=5 ---"
  for_ (the (List Int) [1..5]) $ \_ => do
    Just bn <- pick (genBoundedNat (limit 10) 5)
      | Nothing => printLn "Failed"
    case bn of
      MkBounded n => putStrLn $ "Generated: " ++ show n ++ " (< 5)"
```

Run it:

```bash
echo -e ':exec testBounded' | rlwrap pack repl ./src/Playground.idr
```

The output might be varied:

```text
Main> --- Generating BoundedNat with limit'=5 ---
Generated: 4 (< 5)
Generated: 1 (< 5)
Generated: 1 (< 5)
Generated: 3 (< 5)
Generated: 4 (< 5)
```

The `{auto prf : LT n limit}` constraint ensures that only values less than the limit are generated. `deriveGen` will automatically search for valid `n`
values.

---

## Next Steps

Now that you can generate proof-carrying data, you are ready for more advanced topics:

- **Want to integrate handwritten generators?** Continue to **[Mixing Manual and Automatic Generation](t06-mixing-manual-and-automatic.md)** to see how
`deriveGen` automatically discovers and uses your custom generators.
- **Want to understand the internals?** Continue to **[Under the Hood: Building a deriveGen-like Macro](t11-under-the-hood-a-derivegen-like-macro.md)**
to learn how the derivation engine works.

<!-- idris
main : IO ()
main = do
  testList
  testFuel
  testBounded
-->
