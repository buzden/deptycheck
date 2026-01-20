# 6. Beyond Fuel: A Tutorial on Structural Recursion

In our previous tutorials, we learned that `Fuel` is a crucial safety mechanism. It provides a "generation budget" that prevents `deriveGen` from getting stuck in an infinite loop when generating recursive data.

For a simple type like `List`, the rule is easy to understand: every `Cons` call is a recursive step, so it must spend one unit of fuel. But is this always the case? Is every recursive call equally "expensive"?

### Our Goal

In this tutorial, you will discover that `deriveGen` is smart enough to identify two different kinds of recursion, with very different performance characteristics. You will write two generators:

1.  A generator for a Peano `Nat` type that strictly obeys the fuel budget.
2.  A generator for the indexed `Fin` type that appears to get "free" recursion, defying the budget.

You will learn why this happens, how to recognize the difference between **`SpendingFuel`** and **`StructurallyDecreasing`** recursion, and how you can design your own types to take advantage of this powerful optimization.

### Prerequisites

-   All previous tutorials, especially [Automatic Generator Derivation](04-automatic-generator-derivation.md).

---

## Step 1: The Standard Case - `SpendingFuel` Recursion

Let's start by examining the type of recursion we are already familiar with. We will create a simple Peano number type, where `deriveGen` must spend fuel on every recursive call to guarantee termination.

1.  **Create a new file** named `RecursionTutorial.idr`.

2.  **Add the following code.** This defines our `PNat` (Peano Natural) type and a standard derived generator for it.

    ```idris
    %language ElabReflection

    module RecursionTutorial

    import Deriving.DepTyCheck.Gen
    import Data.Fuel

    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Runner
    import System.Random.Pure.StdGen

    data PNat = PZ | PS PNat

    genPNat : Fuel -> Gen MaybeEmpty PNat
    genPNat = deriveGen
    ```

3.  **The Experiment.** Now, let's write a `main` function to call this generator twice: once with a generous fuel budget (`limit 10`) and once with a very small one (`limit 3`).

    ```idris
    main : IO ()
    main = do
      putStrLn "--- Generating with a large fuel budget (10) ---"
      Just p_large <- pick1 (genPNat (limit 10))
        | Nothing => printLn "Generation failed"
      printLn p_large

      putStrLn "--- Generating with a small fuel budget (3) ---"
      Just p_small <- pick1 (genPNat (limit 3))
        | Nothing => printLn "Generation failed"
      printLn p_small
    ```

4.  **Compile, run, and observe.**

    ```bash
    idris2 --build RecursionTutorial.idr
    ./build/exec/RecursionTutorial
    ```
    Your output will be random, but it will follow a strict pattern:
    ```
    --- Generating with a large fuel budget (10) ---
    PS (PS (PS (PS (PS PZ))))
    --- Generating with a small fuel budget (3) ---
    PS (PS PZ)
    ```
    Notice that the generator with more fuel produced a larger number. The number of `PS` constructors is strictly limited by the fuel you provide. This is because `deriveGen` identifies the `PS` constructor as **`SpendingFuel`**. For each `PS` it generates, it must consume one unit of fuel from the budget. This is the default, safe behavior for simple recursive types.

---

## Step 2: One More Example of Fuel: Generating Trees

We've seen that `deriveGen` takes a `Fuel` argument, which controls recursion. Let's see a concrete example of this. A binary tree is a perfect recursive data structure to experiment with.

1.  **Add a `BinTree` data type and its generator** to your `DeriveTutorial.idr` file.

    ```idris
    data BinTree : Type where
      Leaf : Nat -> BinTree
      Node : BinTree -> Nat -> BinTree -> BinTree

    genBinTree : Fuel -> Gen MaybeEmpty BinTree
    genBinTree = deriveGen
    ```

2.  **Experiment in the REPL.** Now, use `:exec pick1` to run the generator with different fuel limits. You will see the direct impact on the size of the generated tree.

    ```idris
    -- With a very small fuel limit, you will almost always get a Leaf
    :exec pick1 (genBinTree (limit 1))
    -- Leaf 5 : BinTree

    -- With a medium fuel limit, you might get a few nodes
    :exec pick1 (genBinTree (limit 3))
    -- Node (Leaf 2) 7 (Leaf 1) : BinTree

    -- With a large fuel limit, you can get much more complex trees
    :exec pick1 (genBinTree (limit 10))
    -- Node (Node (Leaf 1) 4 (Leaf 0)) 8 (Leaf 9) : BinTree
    ```

This experiment demonstrates the core purpose of `Fuel`: it provides a "depth budget" for generation. Each time `deriveGen` needs to make a recursive call (like generating the sub-trees for a `Node`), it consumes fuel. When the fuel runs out, it will strongly prefer non-recursive constructors (like `Leaf`). This is what prevents infinite loops and gives you control over the complexity of your test data.

---

## Step 2: The Optimization - `StructurallyDecreasing` Recursion

Must `deriveGen` *always* spend fuel on recursion? No. If it can prove that a recursive call is guaranteed to terminate by its structure alone, it can perform a powerful optimization.

A perfect example is `Fin n`, the type of numbers from `0` to `n-1`.

1.  **Add the `Fin` generator** to your `RecursionTutorial.idr` file.
    ```idris
    import Data.Fin

    genFin : (n : Nat) -> Fuel -> Gen MaybeEmpty (Fin n)
    genFin = deriveGen
    ```

2.  **The Counter-Intuitive Experiment.** Now, let's try to generate a `Fin 100`. This would require 100 recursive calls to `FS`. According to our last experiment, this should require at least `limit 100` fuel. But what happens if we only give it `limit 3`?

    ```idris
    main_fin : IO ()
    main_fin = do
      putStrLn "--- Generating a large Fin with a tiny fuel budget (3) ---"
      -- We ask for a Fin up to 100, but only provide fuel for 3 steps!
      Just fin <- pick1 (genFin 100 (limit 3))
        | Nothing => printLn "Generation failed"
      printLn fin
    ```

3.  **Run the experiment** (rename `main_fin` to `main` temporarily) and observe the surprising result.

    ```
    --- Generating a large Fin with a tiny fuel budget (3) ---
    97
    ```
    It works! Even with a tiny fuel budget, it successfully generated a very large `Fin` value. It did not fail or run out of fuel.

4.  **The Explanation.** This is not magic. `deriveGen` is smart enough to analyze the `Fin` type and its `FS` constructor.

    `FS : Fin k -> Fin (S k)`

    It sees that the input `Fin k` is for a type whose index `k` is provably, *structurally smaller* than the output's index `S k`. Because the `Nat` index itself guarantees that the recursion will eventually terminate when it hits `Fin 0`, `deriveGen` does not need to use the `Fuel` parameter as a safety budget. It classifies this kind of recursion as **`StructurallyDecreasing`**.

This optimization allows `deriveGen` to generate values for indexed, recursive data types like `Fin` and `Vect` much more efficiently than it can for simple recursive types like `PNat` or `List`.

---

## Under the Hood: Manual Recursion

How does `deriveGen` actually use the `Fuel`? To understand the magic, it helps to see how you would write a recursive generator by hand. It all comes down to a `case` split on the `Fuel` parameter.

Let's write a generator for a simple `Expr` type. This `genSmartExpr` is a perfect example of how a manual recursive generator is structured.

```idris
data Expr = Lit Nat | Add Expr Expr

-- A smart, handwritten recursive generator
genSmartExpr : Fuel -> Gen MaybeEmpty Expr
genSmartExpr Dry = Lit <$> elements [0..10] -- Base case: Out of fuel, must choose a non-recursive constructor.
genSmartExpr (More fuel) = frequency -- Recursive step: We have fuel, so we can choose.
  [ (1, Lit <$> elements [0..10])
  , (4, Add <$> genSmartExpr fuel <*> genSmartExpr fuel)
  ]
```

This generator explicitly handles the two cases for `Fuel`:

1.  **`genSmartExpr Dry`**: This is the **base case**. When the `Fuel` is `Dry`, we are out of our generation budget. We *must* choose a non-recursive constructor (`Lit`) to ensure the generator terminates.

2.  **`genSmartExpr (More fuel)`**: This is the **recursive step**. We still have fuel to spend. We can `frequency` to choose between the non-recursive `Lit` constructor and the recursive `Add` constructor. When we make the recursive calls (`genSmartExpr fuel`), we do so with the `fuel` from the `More` constructor, which is a smaller amount. This ensures we make progress towards the `Dry` base case.

This `case` split on `Fuel` is the fundamental pattern that `deriveGen` implements for you automatically. Understanding this pattern gives you a clear mental model for how all recursive generation in `DepTyCheck` works.

---

## Congratulations!

You now understand the sophisticated, two-pronged approach `deriveGen` uses to handle recursion safely and efficiently. This knowledge will help you design data types that can be generated more effectively and to reason about the performance of your generators.

In this tutorial, you learned to distinguish between:

*   ✅ **`SpendingFuel` Recursion:** The default, safe strategy for simple recursive types like `List` or a hand-rolled `PNat`, where each recursive step consumes fuel.
*   ✅ **`StructurallyDecreasing` Recursion:** An advanced optimization for indexed types like `Fin` or `Vect`, where `deriveGen` can prove termination from the types alone and does not need to spend fuel.

### Next Steps

This was the final tutorial in the core `DepTyCheck` series. You have progressed from a beginner to a power-user with a deep understanding of the library's architecture. You now have all the tools you need to effectively use property-based testing in your Idris projects.

From here, feel free to explore the `DepTyCheck` source code, especially `Deriving.DepTyCheck.Gen.ConsRecs`, to see the real implementation of the recursion analysis we've discussed, or continue to the next tutorial on [Advanced Derivation Tuning](07-derivation-tuning.md).
