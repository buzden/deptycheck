# 9. Mixing Manual and Automatic Generation

In the [previous tutorial](t05-derivegen-signatures.md), we saw how to control what `deriveGen` generates by crafting function signatures. We also saw how to give it "hints" for primitive types like `String` using the `=>` syntax.

But what if you have a custom data type that needs a special, handwritten generator? `DepTyCheck` provides a powerful, "magic" feature: if you define a generator for a type, `deriveGen` will automatically find it and use it.

## Our Goal

In this tutorial, you will:

1. Define a custom type with a handwritten generator
2. Mark that generator with `%hint` for automatic discovery
3. See `deriveGen` automatically find and use your generator without explicit passing
4. Compare implicit (`%hint`) vs explicit (`@{...}`) generator passing

You will see output like:

```text
--- Testing mixed generation ---
MkUser (MkSpecialString "root") 5
```

---

## Prerequisites

-   Completion of [Tutorial 5: DeriveGen Signatures](t05-derivegen-signatures.md)
-   Understanding of the `=>` syntax for explicit generator constraints
-   Idris2 source file `./src/Mixed.idr` with the header:

```idris
import Test.DepTyCheck.Gen
import Data.Fuel
import Deriving.DepTyCheck.Gen
import System.Random.Pure.StdGen

%language ElabReflection
```

---

## Step 1: Define Types and a Handwritten Generator

Imagine we have a `SpecialString` type that should only ever contain specific, predefined values (e.g., usernames with special privileges). A fully random `String` generator is not appropriate here.

### Create a new file named `Mixed.idr`.

### Define the `SpecialString` type with a `%hint` generator.

```idris
-- A type that needs special generation
data SpecialString = MkSpecialString String

Show SpecialString where
  show (MkSpecialString s) = "MkSpecialString " ++ show s

-- A handwritten generator for SpecialString
%hint
genSpecialString : Gen MaybeEmpty SpecialString
genSpecialString = map MkSpecialString (elements ["admin", "root", "system"])
```

### Define the `User` type that contains `SpecialString`.

```idris
-- Standard domain types
data User = MkUser SpecialString Nat

Show User where
  show (MkUser s i) = "MkUser (" ++ show s ++ ") " ++ show i
```

🔍 **Notice:**

- Signature `Gen MaybeEmpty SpecialString` (no `Fuel ->`) is used for manually defined generators
- The `%hint` pragma marks `genSpecialString` for **auto-implicit search** in Idris 2. It makes this function a candidate for automatic insertion - no explicit `@{genSpecialString}` required!

From Idris 2 docs: `%hint` marks functions for auto search, similar to unnamed type class instances. The compiler prioritizes these hints during unification when explicit arguments are absent.

---

## Step 2: Create the Derived Generator

Now, let's define a generator for `User` using `deriveGen`. A `User` contains a `SpecialString` and a `Nat`. `deriveGen` knows how to generate a `Nat` by default. What will it do for `SpecialString`?

### Add the derived generator to `Mixed.idr`.

```idris
-- Add deriveGen for the User
genUser : Fuel -> (Fuel -> Gen MaybeEmpty SpecialString) => Gen MaybeEmpty User
genUser = deriveGen
```

🔍 **Notice:**

- Automatic derivation by `deriveGen` requires `Fuel ->`
- The constraint `(Fuel -> Gen MaybeEmpty SpecialString) =>` tells `deriveGen` it needs a generator for `SpecialString`
- Normally, you'd pass it explicitly: `genUser @{genSpecialString} fuel`. But `%hint` enables automatic resolution - Idris finds and inserts `genSpecialString` automatically!

---

## Step 3: Test the Generator

Let's create a main function to see our automatic discovery in action.

### Add a test function to `Mixed.idr`.

```idris
main : IO ()
main = do
  putStrLn "--- Testing mixed generation ---"
  Just u <- pick (genUser (limit 10))
    | Nothing => putStrLn "Generation failed"
  printLn u
```

### Compile and run.

```bash
pack build Mixed && pack exec Mixed
```

Expected output (will vary):

```text
--- Testing mixed generation ---
MkUser (MkSpecialString "root") 5
```

---

## When to Use %hint?

`Constraint + %hint` approach is recommended for custom types.

**Pattern:** Mark your generator with `%hint`, add constraint to derived generator:

  ```idris
  %hint
  genMyType : Gen MaybeEmpty MyType
  genMyType = map MkMyType (elements ["a", "b"])

  genContainer : Fuel -> (Gen MaybeEmpty MyType) => Gen MaybeEmpty Container
  genContainer = deriveGen
  ```

**Call site:**
  ```idris
  pick (genContainer fuel)  -- No @{...} needed!
  ```

**Best for:** Custom types where you want automatic discovery with explicit dependencies in the signature.

---

## Next Steps

*   **Continue to the next tutorial:** [Generating GADTs with Proofs](t10-generating-gadts-with-proofs.md) to see how these techniques apply to even more advanced types with proof constraints.
*   **Experiment:** Try creating your own custom type with a `%hint` generator and see if `deriveGen` finds it automatically.
*   **Read more:** Check out the Idris 2 documentation on `%hint` for advanced auto-implicit search patterns.
