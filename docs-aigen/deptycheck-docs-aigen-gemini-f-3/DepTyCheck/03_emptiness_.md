# Chapter 3: Emptiness

Welcome back, aspiring `DepTyCheck` users! In our [previous chapters](01_gen__generator__.md) on [Gen (Generator)](01_gen__generator__.md) and [GenAlternatives](02_genalternatives_.md), we learned how to make our generators randomly produce values. We've seen `Gen NonEmpty String` and `Gen MaybeEmpty (Fin n)`, and you might have wondered what `NonEmpty` and `MaybeEmpty` really mean. This chapter is all about demystifying that!

## What is `Emptiness` and Why Does It Matter?

Imagine you're trying to generate random data for a game. Sometimes, you want to generate a *valid move* for a player. Other times, you might want to try to generate something that is *impossible* to make, to test how your game handles errors.

`Emptiness` is like a guarantee stamp on your generator. It tells you whether a generator is **guaranteed** to always produce a value, or if it **might sometimes fail** to produce one.

*   **`NonEmpty`**: This is like a vending machine that *always* has your snack. You put money in, and you *always* get something out. The generator guarantees it can find a value.
*   **`MaybeEmpty`**: This is like a vending machine that *might* be out of stock. You put money in, and you *might* get a snack, or it might just tell you "sold out!" and take your money back (or, ideally, give it back). The generator *might* fail to find a value.

This concept is crucial in programming with dependent types (like in Idris), because some types inherently have *no possible values*. For example, what is a `Fin 0`? It means a natural number *less than 0*. There are no such numbers! So, a generator for `Fin 0` *must* be `MaybeEmpty` and *must* fail.

Let's look at the example from [Chapter 1: Gen (Generator)](01_gen__generator__.md):

```idris
-- A generator for Fin n (numbers smaller than n).
-- If n is 0, there are no possible values, so it's MaybeEmpty.
genFin : (n : Nat) -> Gen MaybeEmpty (Fin n)
genFin Z     = empty -- If n is 0, it's empty!
genFin (S n) = elements' $ allFins n -- Otherwise, pick from 0 to n.
```

**Explanation:**
*   `genFin : (n : Nat) -> Gen MaybeEmpty (Fin n)`: The `MaybeEmpty` here tells us that `genFin` might not always succeed.
*   `genFin Z = empty`: When `n` is `Z` (which is `0`), we use `empty`. The `empty` generator is a special `Gen MaybeEmpty` that *always* fails. It can't produce a value because `Fin 0` has no inhabitants.
*   `genFin (S n) = elements' $ allFins n`: If `n` is `S k` (meaning `k + 1`), then `Fin (S k)` *does* have values (e.g., `Fin 1` has `0`). So, we can use `elements'` to pick from a list of all possible `Fin` values from `0` up to `k`. Even though this part *always* produces a value, the overall `genFin` has to be `MaybeEmpty` because one of its branches (`genFin Z`) explicitly fails.

## The `Emptiness` Type Inside `DepTyCheck`

Let's peek at how `DepTyCheck` defines `Emptiness` in `src/Test/DepTyCheck/Gen/Emptiness.idr`. It's a very simple data type:

```idris
-- src/Test/DepTyCheck/Gen/Emptiness.idr

public export
data Emptiness = NonEmpty | MaybeEmpty
```

**Explanation:**
*   This simply defines `Emptiness` as a type that can only have two possible values: `NonEmpty` or `MaybeEmpty`. That's it!

`DepTyCheck` uses this type to track the "strength" of a generator's guarantee. `NonEmpty` is considered "stronger" because it gives a stronger guarantee (it will *always* produce something). `MaybeEmpty` is "weaker" because it offers a weaker guarantee (it *might* produce something, or it might not).

### How Emptiness Combines: The `NoWeaker` Relation

When you combine generators with `map`, `bind`, `oneOf`, etc., `DepTyCheck` needs to figure out what the `Emptiness` of the *new* combined generator should be. It uses a special relationship called `NoWeaker` to do this.

`NoWeaker` basically means "is not weaker than." So, `NonEmpty `NoWeaker` MaybeEmpty` means "NonEmpty isn't weaker than MaybeEmpty" (which is true, NonEmpty is stronger). But `MaybeEmpty `NoWeaker` NonEmpty` would be false, because MaybeEmpty *is* weaker.

This is how `DepTyCheck` automatically determines the `Emptiness` of complex generators:

*   **`NonEmpty` + `NonEmpty` = `NonEmpty`**: If you combine two generators that always succeed, the result also always succeeds. (e.g., `elements ["apple"]` and `elements ["banana"]` combined will still always give you one or the other).
*   **`NonEmpty` + `MaybeEmpty` = `MaybeEmpty`**: If even *one* of the generators you combine might fail, the *whole combination* might fail. The system always takes the "safest" (weakest) guarantee.
*   **`MaybeEmpty` + `MaybeEmpty` = `MaybeEmpty`**: If both might fail, the combination definitely might fail.

It's like thinking about the worst-case scenario! If there's *any* chance of failure, the result carries that `MaybeEmpty` label.

Let's illustrate this with our `genAnyFin` example from [Chapter 1: Gen (Generator)](01_gen__generator__.md):

```idris
-- genNat is NonEmpty as it always produces 1, 2, or 3.
genNat : Gen NonEmpty Nat
genNat = elements [1, 2, 3]

-- genFin is MaybeEmpty because genFin Z fails.
genFin : (n : Nat) -> Gen MaybeEmpty (Fin n)
genFin Z = empty
genFin (S n) = elements' $ allFins n

-- What is the Emptiness of genAnyFin?
genAnyFin : Gen MaybeEmpty (n ** Fin n) -- It's MaybeEmpty!
genAnyFin = do
  n : Nat <- genNat
  f : Fin n <- genFin n
  pure (n ** f)
```

**Why is `genAnyFin` `MaybeEmpty`?**

1.  `genNat` is `NonEmpty`.
2.  `genFin n` is `MaybeEmpty` for *any* `n` (because `genFin Z` is `empty`).
3.  Because the `genFin n` step is `MaybeEmpty`, applying `bind` (the `do` notation) with a `MaybeEmpty` generator will make the *overall* result `MaybeEmpty`. Even if `genNat` only produces `1`, `2`, or `3` (for which `genFin` would actually succeed), the *type system* is conservative. Since `genFin` *in general* can be empty, the combined `genAnyFin` must be `MaybeEmpty`.

This is a powerful feature: `DepTyCheck` inherently understands that if there's *any* path through your generator logic that could lead to `empty`, then the whole generator is `MaybeEmpty`.

## Internal Overview: How `DepTyCheck` tracks `Emptiness`

The `Emptiness` type itself is very simple. The complexity comes from how `DepTyCheck` uses it in the `Gen` data type definition and its combinators (`map`, `bind`, `oneOf`).

Let's look at the `Gen` definition from `src/Test/DepTyCheck/Gen.idr` again, focusing on the `Emptiness` parameter (which we'll call `em` for short):

```idris
-- src/Test/DepTyCheck/Gen.idr

data Gen : Emptiness -> Type -> Type where

  Empty : Gen MaybeEmpty a -- Only for MaybeEmpty.

  Pure  : a -> Gen em a -- Can be NonEmpty or MaybeEmpty, just holds a value.

  Raw   : RawGen a -> Gen em a -- Can be NonEmpty or MaybeEmpty; randomness.

  OneOf : (gs : GenAlternatives True alem a) ->
          (0 _ : All IsNonEmpty gs) => -- Constraint: all *internal* generators must be NonEmpty.
          (0 _ : alem `NoWeaker` em) => -- Constraint: the overall 'em' isn't weaker than internal 'alem'.
          Gen em a

  Bind  : (0 _ : biem `NoWeaker` em) => -- Constraint: the overall 'em' isn't weaker than internal 'biem'.
          RawGen c -> (c -> Gen biem a) -> Gen em a

  Labelled : Label -> (g : Gen em a) -> (0 _ : IsNonEmpty g) => Gen em a
```

**Key Takeaways from the `Gen` data type:**

*   **`Empty`**: This constructor *only* exists for `Gen MaybeEmpty a`. You cannot create a `Gen NonEmpty a` using `Empty`. This enforces that `empty` always means `MaybeEmpty`.
*   **`Pure` and `Raw`**: These can be `Gen NonEmpty a` or `Gen MaybeEmpty a`. If you say `Pure 5 : Gen NonEmpty Nat`, it's `NonEmpty`. If you specify `Pure 5 : Gen MaybeEmpty Nat`, that's also valid, but less specific (it's true that `Pure 5` *might* give you a value, but it's guaranteed to).
*   **`OneOf` and `Bind`**: These are where `NoWeaker` comes into play. The constraints `(0 _ : alem `NoWeaker` em)` and `(0 _ : biem `NoWeaker` em)` are proofs that Idris uses to ensure that the resulting `em` is always `NoWeaker` than the intermediate `alem` or `biem`. In simple terms, this means that if any component generator is `MaybeEmpty`, the combined generator will also be `MaybeEmpty`.

Essentially, whenever `DepTyCheck` builds a `Gen` using combinators, it uses these proofs and rules to automatically infer the `Emptiness` of the resulting type. This means you rarely have to manually think about these `NoWeaker` proofs; the type system handles it!

### `Emptiness` Flow Diagram for `genAnyFin`

Let's visualize the `Emptiness` flow for our `genAnyFin` example:

```mermaid
graph TD
    subgraph GenDefinition
        A[genNat: Gen NonEmpty Nat]
        B[genFin: (n: Nat) -> Gen MaybeEmpty (Fin n)]
    end

    subgraph Operation
        C[Bind Operation]
    end

    subgraph Result
        D[genAnyFin: Gen MaybeEmpty (n ** Fin n)]
    end

    A -- "Provides NonEmpty Nat" --> C
    B -- "Called with 'n', potentially MaybeEmpty Fin n" --> C
    C -- "Combines NonEmpty and MaybeEmpty" --> D
    D -- "Result is MaybeEmpty (weakest guarantee)" --> End
```

This diagram shows that:
1. `genNat` gives `NonEmpty`.
2. `genFin` (when used as `genFin n`) gives `MaybeEmpty`.
3. The `Bind` operation combines these. Since one input is `MaybeEmpty`, the `NoWeaker` rule dictates that the output `Emptiness` must be `MaybeEmpty`.

## Conclusion

In this chapter, you've gained a deep understanding of `Emptiness` in `DepTyCheck`:

*   It's a critical concept used to track whether a generator is **guaranteed** (`NonEmpty`) or **might fail** (`MaybeEmpty`) to produce a value.
*   It's especially important for types with no inhabitants (like `Fin 0`).
*   `DepTyCheck` uses the `NoWeaker` relation to automatically combine `Emptiness` types, always choosing the "weakest" (safest) guarantee if any component generator is `MaybeEmpty`.

This `Emptiness` tracking is fundamental to building robust and type-safe property-based tests, allowing `DepTyCheck` to reason about the possibility of generation failure.

Next, we'll explore [CTLabel (Compile-Time Label)](04_ctlabel__compile_time_label__.md), which helps us track specific parts of our generators for better introspection and debugging.

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)