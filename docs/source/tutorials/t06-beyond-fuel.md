# 6. Beyond Fuel: A Tutorial on Structural Recursion

In our previous tutorials, we learned that `Fuel` is a crucial safety mechanism. It provides a "generation budget" that prevents `deriveGen` from getting stuck in an infinite loop when generating recursive data.

For a simple type like `List`, the rule is easy to understand: every `Cons` call is a recursive step, so it must spend one unit of fuel. But is this always the case? Is every recursive call equally "expensive"?

## Our Goal

In this tutorial, you will discover that `deriveGen` is smart enough to identify two different kinds of recursion, with very different performance characteristics. You will write two generators:

1.  A generator for a Peano `Nat` type that strictly obeys the fuel budget.
2.  A generator for the indexed `Fin` type that appears to get "free" recursion, defying the budget.

You will learn why this happens, how to recognize the difference between **`SpendingFuel`** and **`StructurallyDecreasing`** recursion, and how you can design your own types to take advantage of this powerful optimization.

## Prerequisites

-   All previous tutorials, especially [Automatic Generator Derivation](t04-automatic-generator-derivation.md).

---

## Step 1: The Standard Case - `SpendingFuel` Recursion

Let's start by examining the type of recursion we are already familiar with. We will create a simple Peano number type, where `deriveGen` must spend fuel on every recursive call to guarantee termination.

### Create a new file named `RecursionTutorial.idr`

```idris
import Deriving.DepTyCheck.Gen
import Data.Fuel
import Data.Fin

import Test.DepTyCheck.Gen
import System.Random.Pure.StdGen

%language ElabReflection
```

### Add the following code.

This defines our `PNat` (Peano Natural) type and a standard derived generator for it.

```idris
data PNat = PZ | PS PNat

Show PNat where
  show n = show (the Integer (pnatToInteger n))
    where
      pnatToInteger : PNat -> Integer
      pnatToInteger PZ = 0
      pnatToInteger (PS k) = 1 + pnatToInteger k

genPNat : Fuel -> Gen MaybeEmpty PNat
genPNat = deriveGen
```

### The Experiment.

Now, let's write a `main` function to call this generator twice: once with a generous fuel budget (`limit 10`) and once with a very small one (`limit 3`).

```idris
runPeano : IO ()
runPeano = do
  putStrLn "--- Generating with a large fuel budget (10) ---"
  Just p_large <- pick (genPNat (limit 10))
  | Nothing => printLn "Generation failed"
  printLn p_large

  putStrLn "--- Generating with a small fuel budget (3) ---"
  Just p_small <- pick (genPNat (limit 3))
  | Nothing => printLn "Generation failed"
  printLn p_small
```

### Compile, run, and observe.

```bash
idris2 --build RecursionTutorial.idr
./build/exec/RecursionTutorial
```
    Your output will be random, but it will follow a strict pattern:
```text
--- Generating with a large fuel budget (10) ---
PS (PS (PS (PS (PS PZ))))
--- Generating with a small fuel budget (3) ---
PS (PS PZ)
```
    Notice that the generator with more fuel produced a larger number. The number of `PS` constructors is strictly limited by the fuel you provide. This is because `deriveGen` identifies the `PS` constructor as **`SpendingFuel`**. For each `PS` it generates, it must consume one unit of fuel from the budget. This is the default, safe behavior for simple recursive types.

---

## Step 2: StructurallyDecreasing Recursion

Must `deriveGen` *always* spend fuel on recursion? No. If it can prove that a recursive call is guaranteed to terminate by its structure alone, it can perform a powerful optimization.

A perfect example is `Fin n`, the type of numbers from `0` to `n-1`.

### Add the `Fin` generator to your `RecursionTutorial.idr` file.
```idris
genFin : Fuel -> (n : Nat) -> Gen MaybeEmpty (Fin n)
genFin = deriveGen
```

### The Counter-Intuitive Experiment.

Now, let's try to generate a `Fin 100`. This would require 100 recursive calls to `FS`. According to our last experiment, this should require at least `limit 100` fuel. But what happens if we only give it `limit 3`?

```idris
runFin : IO ()
runFin = do
  putStrLn "--- Generating a large Fin with a tiny fuel budget (3) ---"
  -- We ask for a Fin up to 100, but only provide fuel for 3 steps!
  Just fin <- pick (genFin (limit 3) 100)
    | Nothing => printLn "Generation failed"
  printLn fin
```

### Run the experiment and observe the surprising result.

```
    --- Generating a large Fin with a tiny fuel budget (3) ---
    97
```
    It works! Even with a tiny fuel budget, it successfully generated a very large `Fin` value. It did not fail or run out of fuel.

### The Explanation. This is not magic. `deriveGen` is smart enough to analyze the `Fin` type and its `FS` constructor.

    `FS : Fin k -> Fin (S k)`

    It sees that the input `Fin k` is for a type whose index `k` is provably, *structurally smaller* than the output's index `S k`. Because the `Nat` index itself guarantees that the recursion will eventually terminate when it hits `Fin 0`, `deriveGen` does not need to use the `Fuel` parameter as a safety budget. It classifies this kind of recursion as **`StructurallyDecreasing`**.

This optimization allows `deriveGen` to generate values for indexed, recursive data types like `Fin` and `Vect` much more efficiently than it can for simple recursive types like `PNat` or `List`.

---

## Under the Hood: How deriveGen Uses Fuel

### The Mental Model

`deriveGen` generates code that follows a simple pattern: a `case` split on the `Fuel` parameter.

```text
genSomething : Fuel -> Gen MaybeEmpty Something
genSomething Dry      = -- Base case: no fuel, choose non-recursive constructors
genSomething (More f) = -- Recursive case: spend fuel or use optimization
```

- When `Fuel` is `Dry`, the generator **must** choose non-recursive constructors (like `PZ`, `Leaf`, `Nil`)
- When `Fuel` is `More f`, the generator **can** choose recursive constructors (like `PS`, `Node`, `Cons`)
- Each recursive call consumes one unit of `Fuel` (calls with `f` instead of `More f`)
- This guarantees termination: eventually `Fuel` reaches `Dry` and recursion stops

This is why higher `Fuel` values produce larger structures — more recursive steps are allowed before hitting the `Dry` base case.

But the key insight is: **deriveGen doesn't always spend fuel on recursion**. It depends on the type of recursion.

### SpendingFuel: Manual Implementation

For a type like `PNat`, the generated code looks like this:

```idris
genPNat' : Fuel -> Gen MaybeEmpty PNat
genPNat' Dry      = pure PZ  -- Must choose non-recursive constructor
genPNat' (More f) = frequency
  [ (1, pure PZ)           -- Non-recursive option
  , (1, PS <$> genPNat' f)  -- Recursive: spends fuel (calls with f, not More f)
  ]
```

**Notice:** When generating `PS`, we call `genPNat' f` — we pass the **smaller** fuel value. Each recursive step consumes one unit of fuel.

### StructurallyDecreasing: Manual Implementation

For `Fin`, the generated code would be different:

```idris
genFin' : (n : Nat) -> Fuel -> Gen MaybeEmpty (Fin n)
genFin' Z     _    = empty  -- No values for Fin 0
genFin' (S k) fuel = frequency
  [ (1, pure FZ)                  -- Base constructor
  , (1, FS <$> genFin' k fuel) ]   -- Recursive: SAME fuel!
```

**Notice:** When generating `FS`, we call `genFin' k fuel` — with the **same** fuel value!

Why is this safe? Because the **type index** decreases (`S k` → `k`), guaranteeing termination even without spending fuel. The index itself acts as the termination measure.

### The Key Difference

| Aspect | SpendingFuel | StructurallyDecreasing |
|--------|--------------|------------------------|
| **Fuel in recursive call** | `gen f` (less fuel) | `gen fuel` (same fuel) |
| **Termination proof** | Fuel budget decreases | Type index decreases |
| **Max generated size** | Limited by fuel | Limited by index |
| **Examples** | `PNat`, `List a`, `Tree` | `Fin n`, `Vect n a` |

This is the core optimization: when the type system guarantees termination through decreasing indices, `deriveGen` doesn't need to spend fuel. This makes generation of indexed types both faster and capable of producing larger values.

---

## Next Steps

Now that you understand how `deriveGen` handles recursion, you are ready for more advanced topics:

*   **Want to fix biased generators?** Continue to **[Derivation Tuning](t07-derivation-tuning.md)** to learn how to use `ProbabilityTuning` and `GenOrderTuning` instances.
*   **Want to integrate handwritten generators?** Continue to **[Mixing Manual and Automatic Generation](t09-mixing-manual-and-automatic.md)** to see how `deriveGen` discovers and uses your custom generators.
*   **Want to generate types with proof constraints?** Continue to **[Generating GADTs with Proofs](t10-generating-gadts-with-proofs.md)** to see how `deriveGen` handles auto-implicit proof arguments.
