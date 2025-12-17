# 5. Mixing Manual and Automatic Generation

In the [previous tutorial](04-automatic-generator-derivation.md), we saw how `deriveGen` can automatically create generators for complex types. We also saw how to give it "hints" for primitive types like `String` using the `=>` syntax.

But what if you have a custom data type that needs a special, handwritten generator? `DepTyCheck` provides a powerful, "magic" feature: if you define a generator for a type, `deriveGen` will automatically find it and use it.

### Our Goal

We will define a `SpecialString` newtype and write a custom generator for it. We will then create a larger `User` type that contains a `SpecialString` and see how `deriveGen` automatically discovers and integrates our manual generator without any special syntax.

### Prerequisites

This tutorial assumes you have completed [Tutorial 4: Automatic Generator Derivation](04-automatic-generator-derivation.md).

---

## Step 1: A Type That Needs a Custom Generator

Imagine we have a `SpecialString` type that should only ever contain specific, predefined values (e.g., usernames with special privileges). A fully random `String` generator is not appropriate here.

1.  **Create a new file** named `Mixed.idr`.

2.  **Define the types and a handwritten generator.**

    ```idris
    module Mixed

    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Runner
    import Data.Fuel

    -- A type that needs special generation
    data SpecialString = MkSpecialString String

    -- Standard domain types
    data User = MkUser SpecialString Nat

    -- A handwritten generator for SpecialString
    genSpecialString : Fuel -> Gen MaybeEmpty SpecialString
    genSpecialString _ = map MkSpecialString (elements ["admin", "root", "system"])
    ```
    We have defined `genSpecialString` to only produce three possible values. Notice it has the standard `Fuel -> Gen MaybeEmpty ...` signature.

## Step 2: Automatic Derivation Finds the Manual Generator

Now, let's define a generator for `User` using `deriveGen`. A `User` contains a `SpecialString` and a `Nat`. `deriveGen` knows how to generate a `Nat` by default. What will it do for `SpecialString`?

1.  **Add the derived generator** to `Mixed.idr`.

    ```idris
    %language ElabReflection

    -- Add deriveGen for the User
    genUser : Fuel -> Gen MaybeEmpty User
    genUser = deriveGen
    ```

2.  **Test it in the REPL.** Load your `Mixed.idr` file.

    ```idris
    :exec pick1 (genUser (limit 10))
    -- MkUser (MkSpecialString "root") 5 : User

    :exec pick1 (genUser (limit 10))
    -- MkUser (MkSpecialString "admin") 12 : User
    ```

It works! `deriveGen` automatically found and used our `genSpecialString` function when it needed to produce a `SpecialString`. It did this simply by looking for a function in the current scope with the required type signature (`... -> Gen ... SpecialString`).

## When to Use Implicit vs. Explicit (`=>`) Generation

`DepTyCheck` now offers two ways to combine generators:

1.  **Implicit (this tutorial):** `deriveGen` automatically finds a generator in scope for a specific custom type (`SpecialString`).
    *   **When to use:** This is the best method when you have a custom data type and you *always* want to use one specific generator for it.

2.  **Explicit (`=>` syntax):** As seen in Tutorial 4, you can add a `(Fuel -> Gen MaybeEmpty String) =>` constraint to the signature.
    *   **When to use:** This is best when you want to provide a generator for a *primitive* or *built-in* type (like `String`, `Nat`, `List`), or when you want the caller to be able to supply *different* generators in different contexts.

## Congratulations!

You've learned how to seamlessly mix automatic and manual generation, giving you the perfect balance of convenience and control.

### Next Steps

*   **Continue to the next tutorial:** [Generating GADTs and Proof-Carrying Data](./06_generating_gadts.md) to see how these techniques apply to even more advanced types.
