# Chapter 1: deriveGen (Generator Derivation Macro)

Imagine you're trying to test a program that uses custom data structures, like a `Point` with `x` and `y` coordinates, or a `User` with a `name` and `email`. To test these programs effectively, you need lots of example `Point`s or `User`s. Generating this test data by hand can be really tedious and error-prone. You'd have to write code that says, "Okay, for a `Point`, I need a number for `x` and another number for `y`," and so on for every single data type.

This is where `deriveGen` comes in! Think of `deriveGen` as a magical "automatic test data factory". Instead of you writing down detailed instructions for how to create test data for each of your custom types, `deriveGen` looks at how you *defined* your data type and automatically figures out how to build a "generator" for it. You just say "make a generator for this type, please!" and it handles the rest. This makes generating test data much, much simpler.

## What Problem Does `deriveGen` Solve?

Let's say you have a simple data type in Idris 2 for a two-dimensional point:

```idris
data Point = MkPoint Nat Nat
```

If you wanted to create a "generator" for `Point`s manually, you would need to combine existing generators for `Nat` (natural numbers). A `Gen` (short for [Generator](02_gen__generator__.md)) is like a blueprint for creating values of a certain type. You might write something like this:

```idris
-- This is a manual generator for Point
genPointManual : Fuel -> Gen MaybeEmpty Point
genPointManual fuel = do
  x <- genNat fuel -- Get a natural number for x
  y <- genNat fuel -- Get another natural number for y
  pure (MkPoint x y) -- Combine them into a Point
```

This works, but what if your `Point` had more fields? Or what if you had 20 different data types? Writing all these `gen...Manual` functions would get repetitive and boring very quickly!

## The Magic of `deriveGen`

`deriveGen` saves you from this manual effort. It's a special kind of function called a *macro* that runs during compilation. When the compiler sees `deriveGen`, it looks at the type you're trying to generate for and writes all the necessary generator code *for you*.

Here's how you'd use `deriveGen` to create a generator for our `Point` type:

```idris
import Data.Fuel -- We'll learn about Fuel soon!
import Test.DepTyCheck.Gen -- Needed for Gen and MaybeEmpty

data Point = MkPoint Nat Nat

-- Our automatic generator for Point!
genPoint : Fuel -> Gen MaybeEmpty Point
genPoint = deriveGen
```

That's it! Just `genPoint = deriveGen`. The `deriveGen` macro will automatically inspect `Point`, see that it's composed of two `Nat`s, and essentially create the same manual generator we wrote above, but without you typing it out.

The `Fuel` argument is important. Generators in `DepTyCheck` often use `Fuel` to prevent them from running forever, especially when dealing with recursive data types (like lists or trees). Think of `Fuel` as a limited number of "steps" the generator can take. We'll explore this more later, but for now, just know that derived generators usually take `Fuel` as their first argument.

The `Gen MaybeEmpty Point` part means "a generator that can produce `Point` values, and it might sometimes produce no values at all (be empty)". The `MaybeEmpty` part is another detail we'll cover in [Emptiness (NonEmpty, MaybeEmpty)](04_emptiness__nonempty__maybeempty__.md), but for a simple `Point`, it will likely always produce a value.

To enable `deriveGen`, you need to add `%language ElabReflection` at the top of your Idris 2 source file. This line tells the Idris 2 compiler that you're going to use advanced metaprogramming features.

```idris
%language ElabReflection

-- ... rest of your code ...
```

## How `deriveGen` Works (Behind the Scenes)

Let's do a simple walkthrough of what happens when you use `deriveGen`.

```mermaid
sequenceDiagram
    participant You
    participant Idris Compiler
    participant deriveGen Macro
    participant Your DataType (e.g., Point)

    You->>Idris Compiler: Compile my code with `genPoint = deriveGen`
    Idris Compiler->>deriveGen Macro: "Hey, deriveGen, I need a generator for this signature: `Fuel -> Gen MaybeEmpty Point`"
    deriveGen Macro->>Your DataType: "What does `Point` look like?"
    Your DataType-->>deriveGen Macro: "I'm `data Point = MkPoint Nat Nat`"
    deriveGen Macro->>deriveGen Macro: "Okay, I see two `Nat` fields. I need generators for `Nat`."
    deriveGen Macro->>Idris Compiler: "Here's the code for `genPoint`:"
    Note over deriveGen Macro, Idris Compiler: (It hands over code similar to `genPointManual` shown earlier)
    Idris Compiler->>You: Compiles successfully (or tells you if it couldn't figure it out!)
```

Essentially, `deriveGen` is a clever program that runs *inside* the Idris compiler. When it sees your data type, it peeks at its definition (like checking if `Point` has `Nat`s or `String`s). Then, it automatically writes the Idris code for a generator based on that structure.

This process involves some powerful concepts like "elaborator reflection" (which allows the macro to look at and manipulate your code during compilation) and "type analysis" (where it understands the structure of your data type). It also needs to find appropriate generators for the *parts* of your data type (like knowing how to generate a `Nat` for the `Nat` fields in `Point`).

This is a simplified view. Under the hood, `deriveGen` uses many other `DepTyCheck` components to do its job. For example, it needs to figure out the [GenSignature (Generator Signature)](03_gensignature__generator_signature__.md) of the generator it's creating, understand the [Constructors Recursiveness](06_consrecs__constructors_recursiveness__.md) of data types, and check for [Emptiness](04_emptiness__nonempty__maybeempty__.md). These are all topics for future chapters!

The actual code for `deriveGen` in `src/Deriving/DepTyCheck/Gen.idr` looks a bit complex because it's handling all these internal details and making sure the generated code is correct. Here's a very tiny, simplified snippet to show you how `--` macros typically get their information:

```idris
-- From src/Deriving/DepTyCheck/Gen.idr
export %macro
deriveGen : DeriveBodyForType => Elab a
deriveGen = do
  Just signature <- goal
     | Nothing => fail "The goal signature is not found..."
  -- ... deriveGen then uses 'signature' to figure out what type it needs to generate for
  tt <- deriveGenExpr signature
  check tt
```

This `goal` part is where the `deriveGen` macro asks the Idris compiler, "What type is this `deriveGen` supposed to produce?" In our example, it would get `Fuel -> Gen MaybeEmpty Point`. From this, it can deduce that it needs to build a generator for `Point` and process its constructors (`MkPoint`).

## Conclusion

In this chapter, you've learned that `deriveGen` is a powerful macro that automatically creates test data generators for your custom data types. Instead of manually writing generator code, you can use `deriveGen` to have it automatically generated for you, saving time and effort. This abstraction significantly simplifies the process of creating test data, allowing you to focus on testing your program logic rather than on how to generate the inputs.

Next, we'll dive deeper into the core concept of a generator itself: [Gen (Generator)](02_gen__generator__.md).

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)