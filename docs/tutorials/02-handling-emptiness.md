# 2. Handling Emptiness: When a Type Has No Values

In the [first tutorial](01_Generator_Monad.md), we used `Gen1`, which is a guarantee—a promise—that a value can always be generated. This works perfectly for types like `Nat` or `String` that always have inhabitants.

But what happens when a type might be **uninhabited** (have no values at all) under certain conditions?

This is a common scenario in dependently-typed programming. A perfect example is `Fin n`, the type of natural numbers from `0` up to `n-1`.

- `Fin 3` has three inhabitants: `0`, `1`, and `2`.
- `Fin 1` has one inhabitant: `0`.
- But what about `Fin 0`? It asks for a number in the range `0` to `-1`. There are no such numbers. This type is **uninhabited**.

It is impossible to write a generator that produces a value of type `Fin 0`, because none exist. Our testing library must be able to handle this gracefully.

### Our Goal

In this tutorial, you will learn how to write safe generators for types that might be empty. You will build a correct generator for `Fin n` and see how to handle its results safely. By the end, you will understand how `DepTyCheck` allows you to run:

```idris
-- This will produce a valid result, wrapped in `Just`
:exec pick (genFin 3)
Just 1 : Maybe (Fin 3)

-- This will safely produce `Nothing`, because `Fin 0` is empty
:exec pick (genFin 0)
Nothing : Maybe (Fin 0)
```

### Prerequisites

This tutorial assumes you have completed the first tutorial, ["The Generator Monad"](01-generator-monad.md).

---

## Step 1: Discovering the Problem

Let's start by trying to write a generator for `Fin n` using only the tools we know from the first tutorial.

1.  **Create a new file** named `EmptyTutorial.idr`.

2.  **Add the following code** to it. We need to import `Data.Fin` along with our usual testing modules.

    ```idris
    module EmptyTutorial

    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Runner
    import Data.Fin
    import Data.Vect
    ```

3.  Now, **try to write a `Gen1` generator** for `Fin n`. We can handle the case where `n` is greater than zero, but the `Z` (zero) case presents a major problem.

    ```idris
    -- This is an INTENTIONALLY INCORRECT generator to show the problem
    genFinIncorrect : (n : Nat) -> Gen1 (Fin n)
    genFinIncorrect (S k) = elements' (allFins k)
    genFinIncorrect Z     = ? -- What could we possibly write here?
    ```

    We have a problem. In the `(S k)` case, we can list all possible values of `Fin (S k)` and use `elements'` to create a generator. But in the `Z` case, what can we do?

    The type is `Gen1 (Fin 0)`, but `Fin 0` has no values. We can't use `pure` because we don't have a value to give it. We're stuck.

This is the problem `DepTyCheck` is designed to solve. We need a way to tell the system that a generator is *intentionally* empty.

---

## Step 2: Introducing `Gen0` and `empty`

`DepTyCheck` provides two new tools to solve this exact problem:

-   **`Gen0 a`**: A type for a generator that *might* produce a value of type `a`. Think of it as a "possibly empty" recipe.
-   **`empty`**: A specific generator of type `Gen0 a` that is *guaranteed* to produce nothing. It's the recipe for an empty set.

Let's use these to fix our incorrect generator.

1.  **Add the correct `genFin` generator** to your `EmptyTutorial.idr` file.

    ```idris
    -- A correct, safe generator for Fin n
    genFin : (n : Nat) -> Gen0 (Fin n)
    genFin Z     = empty
    genFin (S k) = elements' (allFins k)
    ```

    The changes are small but critical:
    - The return type is now `Gen0 (Fin n)`, which signals that the result may be empty.
    - In the `Z` case, we can now simply return `empty`. This correctly tells `DepTyCheck` that the recipe for `Fin 0` produces nothing.


---

## Step 3: Running a `Gen0` Generator

Because a `Gen0` generator might not produce a value, we can't use `pick1` (which promises to return one value). Instead, we must use `pick`, which safely handles the possibility of emptiness.

- `pick1 gen` returns `a`
- `pick gen` returns `Maybe a`

Let's see this in action.

1.  **Run `genFin` for both an inhabited case (`Fin 3`) and an empty case (`Fin 0`)** in your REPL.

    First, the inhabited case:
    ```idris
    :exec pick (genFin 3)
    ```
    The result will be a `Fin 3` value wrapped in a `Just`, because a value could be generated:
    ```idris
    Just 1 : Maybe (Fin 3)
    ```

2.  Now, run the empty case:
    ```idris
    :exec pick (genFin 0)
    ```
    Because we used `empty` in our definition for `genFin Z`, `DepTyCheck` knows this generator can't produce a value, and `pick` safely returns `Nothing`:
    ```idris
    Nothing : Maybe (Fin 0)
    ```

This is the core of safe, dependently-typed testing. The type system allows us to model that some generations are impossible, and the runner (`pick`) allows us to handle those cases gracefully at runtime without any crashes.\n\n---\n\n## Step 4: Filtering with `suchThat`

A type can also be effectively "empty" if we filter its values so much that none remain. `DepTyCheck` provides `suchThat` for this.

`g `suchThat` p` takes a generator `g` and a predicate (a function that returns a `Bool`) `p`. It runs the generator `g`, and if the value it produces satisfies `p`, it returns it. If not, the generation fails for that attempt.

Because the condition might never be met, `suchThat` always returns a `Gen0`.

1.  **Add these two generators** to your `EmptyTutorial.idr` file.

    ```idris
    isEven : Nat -> Bool
    isEven n = n `mod` 2 == 0

    -- A generator that tries to find an even number between 0 and 10.
    -- This will sometimes succeed and sometimes fail (if `choose` picks an odd number).
    genEven : Gen0 Nat
    genEven = choose (0, 10) `suchThat` isEven

    -- A generator that tries to find a number greater than 10 in a range where none exist.
    -- This recipe is impossible and will always be empty.
    genImpossible : Gen0 Int
    genImpossible = choose (1, 10) `suchThat` (> 10)
    ```

2.  **Run them both in the REPL** using `pick`.

    ```idris
    -- This might return Just 4, Just 8, or Nothing
    :exec pick genEven

    -- This will ALWAYS return Nothing
    :exec pick genImpossible
    ```

This demonstrates another critical aspect of `Gen0`: it allows for speculative generation that might fail, giving you a powerful way to define complex properties.

---

## Congratulations!

You can now write safe, robust generators for complex dependent types and are prepared to handle the full range of data-generating scenarios.

In this tutorial, you learned how to:

*   ✅ Identify types that can be uninhabited (empty).
*   ✅ Use `Gen0` to define a generator that might not produce a value.
*   ✅ Use `empty` to explicitly mark a generation path as impossible.
*   ✅ Use `pick` to safely run a `Gen0` and handle the resulting `Maybe` value.
*   ✅ Create filtered generators with `suchThat` and understand why they must also be `Gen0`.

### Next Steps

Now that you've mastered manual generation for both simple and complex types, it's time to see how `DepTyCheck` can do this work for you automatically.

*   **Next Tutorial:** Continue to **[Measuring Your Test Coverage](./03-measuring-test-coverage.md)** to learn how to analyze the quality of your generated data.
