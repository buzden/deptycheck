# Chapter 8: Derivation Tuning

In the [previous chapter on Recursion and Weight Analysis (`ConsRecs`)](07_recursion_and_weight_analysis___consrecs___.md), we saw how `deriveGen` acts like a "safety inspector," automatically analyzing our data types to figure out recursion and assign default weights for choosing constructors. This automatic analysis is incredibly powerful and works perfectly for most cases.

But what if you, the programmer, know something that `deriveGen` doesn't? What if the automatic strategy isn't quite what you need? Sometimes, you need to grab the steering wheel and give the derivation process a little guidance.

This is where **Derivation Tuning** comes in. It provides you with a set of "control knobs" to fine-tune the automatic derivation process, giving you ultimate control over how your test data is generated.

## Knob 1: Controlling Generation Order with `GenOrderTuning`

`deriveGen` is very clever at figuring out the order to generate a constructor's arguments, especially for dependent types (as we saw in [Chapter 6](06_constructor_specific_derivation___derivebodyrhsforcon___.md)). But sometimes, a data type can be
so constrained that the automatic analysis struggles.

Let's imagine a data type that represents a pair of numbers where the first must be strictly less than the second.

```idris
data LtPair : Type where
  MkPair : (n : Nat) -> (m : Nat) -> (IsLT n m) -> LtPair
```
*   `IsLT n m` is a type that only has a value if `n` is actually less than `m`. It's a proof.

The default strategy for `deriveGen` might be:
1.  Generate a random `n`.
2.  Generate a random `m`.
3.  *Try* to generate a proof that `n < m`.

This is inefficient! If it picks `n=5` and `m=2`, the third step will fail. The generator will have to try over and over again until it gets lucky. We know a better way:

1.  Generate a random `m`.
2.  Generate a random `n` that is *guaranteed* to be less than `m`.
3.  The proof will now be easy to generate.

`GenOrderTuning` lets us teach this "smarter" strategy to `deriveGen`.

### How to Use `GenOrderTuning`

We can implement the `GenOrderTuning` interface for our `MkPair` constructor to tell `deriveGen` our preferred order.

**Analogy:** This is like leaving a special note for the assembly robot that says, "For this specific part, ignore your default instructions and follow these steps instead."

```idris
import Deriving.DepTyCheck.Gen.Tuning

-- Tell deriveGen how to handle the "MkPair" constructor
GenOrderTuning "MkPair".dataCon where
  isConstructor = itIsConstructor
  deriveFirst _ _ = [`{m}, `{n}]
```
Let's break down this tuning "note":
*   `GenOrderTuning "MkPair".dataCon`: We are providing tuning instructions for the constructor named "MkPair".
*   `isConstructor = itIsConstructor`: This is a small piece of compile-time magic that confirms "MkPair" is indeed a valid constructor name.
*   `deriveFirst _ _ = [`{m}, `{n}]`: This is the core instruction. It says, "When building `MkPair`, please generate the argument named `m` first, then the argument named `n`." The proof argument isn't mentioned, so it will be generated last by default.

Now, when you use `deriveGen` for `LtPair`, it will see this note and use our more efficient, custom strategy for the `MkPair` constructor.

## Knob 2: Controlling Data Distribution with `ProbabilityTuning`

In the last chapter, we learned that `deriveGen` sets up a lottery to choose between constructors, with each one getting a default "weight" of 1. For a `List`, this means `Nil` and `(::)` have a 50/50 chance of being picked (when there is fuel).

This gives a good general distribution of list lengths. But what if you want to specifically test how your code handles very long lists? Or what if you want to generate lots of empty lists? `ProbabilityTuning` lets you rig the lottery.

### How to Use `ProbabilityTuning`

Let's tune the generator for `List a` to produce, on average, longer lists. We can do this by giving the recursive `(::)` constructor more lottery tickets.

**Analogy:** `ProbabilityTuning` is like telling the lottery manager, "I know everyone usually gets one ticket, but for this specific contestant, give them ten tickets instead."

```idris
import Deriving.DepTyCheck.Gen.Tuning

-- Give the list 'cons' constructor more weight
ProbabilityTuning "(::)".dataCon where
  isConstructor = itIsConstructor
  tuneWeight _ = 10
```

Here’s what this does:
*   `ProbabilityTuning "(::)".dataCon`: We're providing tuning instructions for the `(::)` constructor.
*   `tuneWeight _ = 10`: The `tuneWeight` function takes the default weight (which is `1`) and returns the new weight we want to use. Here, we're saying the new weight should be `10`.

Now, when `deriveGen` builds a generator for `List`, it will set up the lottery like this:

```idris
-- Conceptually, the generated code is now:
genList (More fuel) =
  frequency
    [ (1,  genForNil)  -- `Nil` still has 1 ticket
    , (10, genForCons) -- `(::)` now has 10 tickets!
    ]
```
The `(::)` constructor is now 10 times more likely to be chosen than `Nil`, which will lead to the generation of much longer lists on average.

## Under the Hood: How Tuning Works

You might be wondering, "How does `deriveGen` find my tuning instructions?" It's not magic, but a clever use of Idris's interface system at **compile-time**.

When `deriveGen` is building a generator, it pauses at key decision points and asks the Idris compiler a question.

Here is a simplified walkthrough for our `LtPair` example:

```mermaid
sequenceDiagram
    participant DG as deriveGen Macro
    participant D4C as DeriveBodyRhsForCon
    participant IC as Idris Compiler
    participant Tuning as Your `GenOrderTuning` Impl
    participant GC as Generated Code

    DG->>D4C: Please build a recipe for the `MkPair` constructor.
    D4C->>IC: Hey, is there an implementation of `GenOrderTuning` for "MkPair"?
    IC->>Tuning: (Finds your implementation)
    Tuning-->>IC: Yes! The user wants the order `[m, n]`.
    IC-->>D4C: The user has specified the order `[m, n]`.
    D4C->>GC: Okay, I have my orders! I will generate `m`, then `n`, then the proof.
    GC-->>D4C: Code for `do { m <- genM; n <- genN; ... }` is built.
```
The process is similar for `ProbabilityTuning`. When the [`DeriveBodyForType`](05_single_type_derivation_core___derivebodyfortype___.md) component is about to set up the `frequency` lottery, it asks the compiler if there are any `ProbabilityTuning` implementations for the constructors involved. If it finds one, it uses the provided `tuneWeight` to adjust the number of lottery tickets.

The key takeaway is that this is not a runtime check. Your tuning instructions are read by the compiler and are baked directly into the generated code, making them very efficient.

### The Interfaces in the Code

These "control knobs" are defined as standard Idris `interface`s in the file `src/Deriving/DepTyCheck/Gen/Tuning.idr`.

```idris
-- File: src/Deriving/DepTyCheck/Gen/Tuning.idr

-- The knob for generation order
public export
interface GenOrderTuning (0 n : Name) where
  isConstructor : (con : IsConstructor n ** GenuineProof con)
  deriveFirst : ... -> List $ ConArg ...

-- The knob for constructor probability
public export
interface ProbabilityTuning (0 n : Name) where
  0 isConstructor : (con : IsConstructor n ** GenuineProof con)
  tuneWeight : Nat1 -> Nat1
```
By implementing these interfaces, you are hooking directly into the compile-time logic of `deriveGen` and customizing its behavior.

## Conclusion

Derivation Tuning provides the essential "escape hatches" you need when the automatic derivation process isn't perfectly suited to your specific testing needs.

You've learned about two powerful control knobs:
*   **`GenOrderTuning`**: Lets you manually specify the generation order of a constructor's arguments, which is critical for solving complex dependencies.
*   **`ProbabilityTuning`**: Allows you to adjust the relative weight or likelihood of constructors, giving you fine-grained control over the distribution of your test data.

With these tools, you can guide `deriveGen` to produce exactly the kind of test data you need. But now that we can generate all this amazing data, how can we be sure that it's actually exercising all the important parts of our functions? In the next chapter, we'll explore how `DepTyCheck` can help answer that question with [Test Coverage Analysis](09_test_coverage_analysis_.md).

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)