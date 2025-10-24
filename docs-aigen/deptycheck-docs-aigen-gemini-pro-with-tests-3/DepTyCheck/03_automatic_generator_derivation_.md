# Chapter 3: Automatic Generator Derivation

In our [last chapter](02__gen__monad_.md), we learned how to write recipes for random data ourselves using the [`Gen` Monad](02__gen__monad_.md). We saw that we can chain these recipes together to create complex, dependent values. This is powerful, but let's be honest—if you have a large data type, writing a detailed generator for it by hand can feel like writing a 100-page cookbook for a single meal. It's tedious and easy to get wrong.

What if we could skip writing the recipe? What if we could just show the compiler a picture of the final dish (our data type) and have it figure out the recipe automatically?

Welcome to `DepTyCheck`'s "auto-chef" feature: Automatic Generator Derivation.

### The Problem: Writing Recipes is a Chore

Imagine we have a standard, recursive data type for natural numbers:

```idris
data Nat = Z | S Nat
```
A `Nat` is either `Z` (zero) or the successor `S` of another `Nat`.

If we wanted to write a generator for this by hand, following the patterns from the last chapter, it might look something like this:

```idris
-- This is what we'd have to write manually
manualGenNat : (fuel : Nat) -> Gen MaybeEmpty Nat
manualGenNat Z     = pure Z
manualGenNat (S n) = oneOf [ pure Z
                           , do rec_n <- manualGenNat n
                                pure (S rec_n)
                           ]
```

This isn't terribly difficult for `Nat`, but notice the details we have to get right. We need to handle the base case (`Z`), the recursive case (`S n`), and combine them so that we produce both short and long chains of `S`. Now imagine doing this for a type with ten constructors and dozens of fields!

This is where automation becomes a lifesaver.

### The Solution: Ask the Chef to `deriveGen`

`DepTyCheck` provides a powerful macro called `deriveGen` that does all this hard work for you. Instead of writing the recipe, you just state what you want and let the compiler write the implementation.

Here's how you'd create a generator for `Nat` automatically:

```idris
%language ElabReflection

genNat : Fuel -> Gen MaybeEmpty Nat
genNat = deriveGen
```

That's it. That's the entire implementation. At compile-time, `deriveGen` inspects the `Nat` data type, understands its structure (`Z | S Nat`), and writes a correct and complete generator for you, which gets compiled as if you had written it by hand.

Let's break down the new pieces in that snippet:

*   `%language ElabReflection`: This is a special command for the Idris compiler. Think of it as flipping a switch that gives our code "superpowers" to inspect and even generate other code during compilation. `deriveGen` needs this power to look at your data types.
*   `Fuel`: What's this `Fuel` argument? For a recursive type like `Nat`, we could have `S(S(S(...)))` go on forever. `Fuel` is a simple mechanism to prevent infinite loops. It's like telling the auto-chef, "You have enough energy to cook a dish up to 10 levels of complexity." Each time the generator calls itself recursively (to make the inner `Nat` for an `S`), it uses up some fuel. When the fuel runs out, it stops recursing.
*   `deriveGen`: This is the magic macro itself. It's a placeholder that tells the compiler, "Please analyze the type signature I've provided (`Fuel -> Gen MaybeEmpty Nat`) and generate the code for me here."

### How It Works: A Look Inside the Kitchen

So what actually happens when the compiler sees `genNat = deriveGen`? It's a fascinating process that all happens before your program even runs.

Imagine you're the manager of a robotic kitchen.

```mermaid
sequenceDiagram
    participant Dev as You (Developer)
    participant Idris2 as Compiler
    participant Macro as `deriveGen` Macro
    participant API as Reflection API

    Dev->>Idris2: Compile my file!
    Idris2->>Idris2: I see `genNat : ...` and its body is `deriveGen`.
    Idris2->>Macro: Hey, `deriveGen`, it's your turn. The goal is to create a function of type `Fuel -> Gen MaybeEmpty Nat`.
    Macro->>API: Reflection API, tell me about the type `Nat`. What does it look like?
    API-->>Macro: `Nat` is a data type with two constructors: `Z` (which takes no arguments) and `S` (which takes one argument of type `Nat`).
    Macro->>Macro: Okay. To make a `Nat`, I can either pick `Z` or `S`. I'll use `oneOf` to combine them.
    Macro->>Macro: The recipe for `Z` is easy: `pure Z`.
    Macro->>Macro: The recipe for `S` is recursive. I must first generate a `Nat`, then wrap it in `S`. I'll make a recursive call to `genNat`, but with less `Fuel`.
    Macro-->>Idris2: Here is the code I generated: `\fuel => case fuel of Z => pure Z; (S n) => oneOf [...]`. (This is a simplified representation).
    Idris2->>Idris2: Great! I'll replace `deriveGen` with this code and finish compiling.
    Idris2-->>Dev: Compile successful!
```

This compile-time reflection is what makes `deriveGen` so powerful. It's not just a simple function; it's an intelligent system that analyzes your types and engineers a correct generator based on that analysis.

### The Machinery Under the Hood

The code that powers this magic lives in `src/Deriving/DepTyCheck/Gen.idr`. While the full implementation is complex, we can look at the high-level logic.

The process starts when `deriveGen` is called. The macro first needs to understand what kind of generator it's supposed to build. It does this by inspecting its own type signature using a function that is conceptually similar to this:

```idris
-- A simplified view of the signature analysis
checkTypeIsGen : (signature : TTImp) -> Elab ...
checkTypeIsGen signature = do
  -- Break `Fuel -> Gen MaybeEmpty Nat` into its parts
  let (args, resultType) = unPi signature
  -- args => [Fuel]
  -- resultType => Gen MaybeEmpty Nat

  -- Break `Gen MaybeEmpty Nat` into its parts
  let (gen, emptiness, targetType) = unApp resultType
  -- gen => Gen
  -- emptiness => MaybeEmpty
  -- targetType => Nat

  -- ... and so on
```
This function, `checkTypeIsGen`, acts like a detective. It deconstructs the type signature to extract all the crucial pieces of information:
*   The fuel argument (`Fuel`).
*   That the result is a `Gen`.
*   That it's `MaybeEmpty`.
*   And most importantly, the **target type** to be generated (`Nat`).

Once it has this information, it passes it along to the core derivation logic. This logic is a collaboration between several modules:
*   The **[Derivation Orchestrator](04_derivation_orchestrator_.md)** acts as the project manager, figuring out all the types that need generators.
*   The **[Single-Type Derivation Core](05_single_type_derivation_core_.md)** focuses on generating the code for one type at a time, like our `Nat`.
*   The **[Constructor Body Derivation](06_constructor_body_derivation_.md)** handles the logic for each individual constructor (like `Z` and `S`).

We will explore each of these components in the upcoming chapters. For now, the key takeaway is that `deriveGen` kicks off a sophisticated, multi-stage analysis at compile-time to automatically write your generator code.

### Conclusion

In this chapter, we've unlocked one of `DepTyCheck`'s most powerful features: automatic generator derivation. We learned that:

*   Writing generators by hand for complex types is tedious and error-prone boilerplate.
*   The `deriveGen` macro acts like an "auto-chef", analyzing a data type at compile-time and automatically writing a correct generator for it.
*   This process uses **Elaborator Reflection** to inspect type definitions.
*   The `Fuel` argument is used to control recursion and prevent infinite generation for recursive data types.

By using `deriveGen`, you can massively reduce the amount of setup code needed for property-based testing, allowing you to focus on what really matters: writing the properties themselves. You get all the power of the [`Gen` Monad](02__gen__monad_.md) without the manual labor.

But what happens when `deriveGen` needs to create generators for multiple, interconnected types? How does it manage that whole process? That's the job of the [Derivation Orchestrator](04_derivation_orchestrator_.md), which we'll explore next.

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)