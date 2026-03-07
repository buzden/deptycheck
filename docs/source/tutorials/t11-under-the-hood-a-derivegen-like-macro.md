# 11. Under the Hood: Building a `deriveGen`-like Macro

In the previous tutorials, we wielded the power of `deriveGen` and even learned how to tune it. In this final, advanced tutorial, we will go behind the curtain to understand how the magic happens. We will demystify `deriveGen` by building our own simplified version from scratch.

> **Disclaimer: This is a very Advanced Tutorial.** We will be interacting directly with the core interfaces of `DepTyCheck`'s derivation engine and using compile-time reflection (`ElabReflection`). This tutorial is for those who are not just users, but are curious about the mechanics of the library itself, or may even wish to contribute.

## Our Goal: Understanding Constructor Generation

`deriveGen` automatically generates values for each constructor. But how does it work internally? We will create a custom derivation strategy that shows exactly what arguments each constructor receives.

By building a custom strategy from scratch, you will understand the core components of the `DepTyCheck` engine and how to extend it.

## The Architecture of Derivation

`DepTyCheck`'s derivation is a two-level hierarchy:

### The "Type Expert" (`DeriveBodyForType`)

Its job is to know about a *whole type*. It looks at all the constructors and generates the top-level code that *chooses* between them. This is where `Fuel` fuel management happens.

### The "Constructor Expert" (`DeriveBodyRhsForCon`)

It knows how to build *one specific constructor*. For each constructor, it generates the code that produces the constructor's arguments.

In this tutorial, we will implement our own Constructor Expert that uses custom logic for generating arguments.

## Prerequisites

-   A good understanding of Idris's interfaces (type classes).
-   Completion of all previous tutorials, especially [Advanced Derivation Tuning](t10-derivation-tuning.md).

---

## Step 1: The Setup

First, let's set up our file and define a data type where we want custom argument generation.

### Create a new file

Create a new file named `CustomGen.idr`.

### Add the necessary setup

We need imports to interact with the derivation engine's internal interfaces.

```idris
import Deriving.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen.ForOneType.Interface
import Deriving.DepTyCheck.Gen.ForOneType.Impl
import Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Interface
import Deriving.DepTyCheck.Gen.ConsRecs
import Deriving.DepTyCheck.Gen.Signature

import Test.DepTyCheck.Gen
import Data.Fuel
import System.Random.Pure.StdGen

%language ElabReflection

-- A simple type with two non-recursive constructors for demonstration purposes
data UserStatus = Active String | Inactive String

Show UserStatus where
  show (Active name) = "Active " ++ show name
  show (Inactive reason) = "Inactive " ++ show reason
```

Both constructors are non-recursive (only contain `String`), so `MainCoreDerivator` will choose between them randomly. Our custom logic will control the **arguments** they receive.

---

## Step 2: Implement the Constructor Logic

Our task is to write a custom strategy for how constructors generate their arguments. We'll create a named implementation of `DeriveBodyRhsForCon` that gives us full control.

### Create a custom constructor generator

We'll generate `Active` with predefined usernames and `Inactive` with predefined reasons.

```idris
[CustomStatusGen] DeriveBodyRhsForCon where
  consGenExpr sig con givs _ = do
    -- Check which constructor we're generating for
    logMsg "tutorial.consGenExpr" 1 $ "con.name: " ++ show con.name
    pure $ if (dropNS con.name) == `{Active}
      then `(Active <$> elements ["Alice", "Bob", "Charlie"])
      else `(Inactive <$> elements ["vacation", "sick", "offline"])
```

> [!NOTE]\
> -   One named implementation handles **all** constructors for the type
> -   We use `con.name` to check which constructor we're generating
> -   We don't call `deriveGen` recursively - we generate arguments **directly**
> -   `elements` is a generator from `Test.DepTyCheck.Gen` that picks from a list
> -   We return Idris code templates using quotation syntax `` `( ... ) ``

This shows the key insight: `consGenExpr` returns **code templates** (TTImp), not values. We're building the generator at compile time!

To watch logging messages you need force Idris2 to recompile the module completely because after the compile time it will no show any logs, for example: `rlwrap pack --extra-args="--log 1" repl ./src/CustomGen.idr`

---

## Step 3: Create the Type Derivator

Now we wrap our constructor strategy into a complete derivation pipeline using `MainCoreDerivator`.

### Wrap the strategy

```idris
-- Wrap our strategy into a full type derivator
CustomDerivator : DeriveBodyForType
CustomDerivator = MainCoreDerivator @{CustomStatusGen}
```

> [!NOTE]\
> -   `MainCoreDerivator` adapts `DeriveBodyRhsForCon` → `DeriveBodyForType`
> -   The `@{CustomStatusGen}` syntax passes our named implementation
>    `MainCoreDerivator` handles fuel management and constructor selection automatically

---

## Step 4: Use the Custom Derivator

Now we can use our custom derivator with `deriveGen`.

### Define the generator

```idris
-- The generator that uses our custom derivator
genUserStatus : Fuel -> Gen MaybeEmpty UserStatus
genUserStatus = deriveGen @{CustomDerivator}
```

> [!NOTE]\
> -   Same signature as any derived generator: `Fuel -> Gen MaybeEmpty UserStatus`
> -   We pass our derivator using the `@{...}` syntax
> -   No need for a separate "macro" - `deriveGen` works directly!

---

## Step 5: Test It

Let's run it and see that our custom argument generation works.

```idris
main : IO ()
main = do
  putStrLn "--- Testing custom derivation ---"
  for_ (the (List Int) [1..15]) $ \_ => do
    Just s <- pick (genUserStatus (limit 20))
      | Nothing => printLn "Generation failed"
    printLn s
```

### Run and analyze

```bash
echo -e ':exec main' | rlwrap pack repl ./src/CustomGen.idr
```

Expected output will show both constructors with our custom arguments:

```text
--- Testing custom derivation ---
Active "Alice"
Inactive "vacation"
Active "Bob"
Active "Charlie"
Inactive "sick"
Active "Alice"
Inactive "offline"
Active "Bob"
Inactive "vacation"
Active "Charlie"
Active "Alice"
Inactive "sick"
Active "Bob"
Inactive "offline"
Active "Charlie"
```

You'll see both `Active` and `Inactive` constructors (chosen randomly by `MainCoreDerivator`), each with our custom predefined values. This proves our custom constructor logic is working!

---

## Understanding the Partnership

You might have noticed something interesting in Step 3: `CustomDerivator`

The `@{CustomStatusGen}` syntax passes our Constructor Expert to `MainCoreDerivator`.

Internally, `MainCoreDerivator` does something like this (simplified):

```text
DeriveBodyRhsForCon => DeriveBodyForType where
  canonicBody sig n = do
    -- For EACH constructor, call the Constructor Expert
    consBodies <- for sig.targetType.cons $ \con =>
      consGenExpr sig con empty (var "fuel")
    -- Then choose which one to call (oneOf, frequency, etc.)
    -- ... fuel management and constructor selection ...
```

This is the delegation pattern in action!

---

## Step 6: Building a Minimal Type Expert

Now let's implement our own Type Expert to see the delegation explicitly. We'll create a minimal version that works for non-recursive types like `UserStatus`.

### Implement EduDerivator

```idris
-- A minimal Type Expert that shows delegation explicitly
[EduDerivator] DeriveBodyRhsForCon => DeriveBodyForType where
  canonicBody sig n = do
    let ctorsUserStatus@[_, _] = sig.targetType.cons
      | _ => fail "Bad example"

    activeGen <- consGenExpr sig (index 0 ctorsUserStatus) empty (var "fuel")
    inactiveGen <- consGenExpr sig (index 1 ctorsUserStatus) empty (var "fuel")

    logMsg "tutorial.canonicBody" 1 $ "activeGen: " ++ show activeGen
    logMsg "tutorial.canonicBody" 1 $ "inactiveGen: " ++ show inactiveGen

    pure [ callCanonic sig n (bindVar "fuel") (replicate sig.givenParams.size implicitTrue) .= `(oneOf [~activeGen, ~inactiveGen]) ]
```

**This is a conceptual example.**

> [!NOTE]\
> -   The constraint `DeriveBodyRhsForCon =>` means we NEED a Constructor Expert
> -   We explicitly call `consGenExpr` for each constructor
> -   For demonstration purposes of non-recursive types, we just use `oneOf`, so no fuel management needed
> -   `callCanonic` builds the function call: `genName fuel = ...`
> -   This is a simplified version of what `MainCoreDerivator` does

### Use EduDerivator with our Constructor Expert

```idris
-- Compose EduDerivator with CustomStatusGen
EduCustomDerivator : DeriveBodyForType
EduCustomDerivator = EduDerivator @{CustomStatusGen}

-- Generator using our educational derivator
genUserStatusEdu : Fuel -> Gen MaybeEmpty UserStatus
genUserStatusEdu = deriveGen @{EduCustomDerivator}
```

### Test it

```idris
testEdu : IO ()
testEdu = do
  putStrLn "--- Testing EduDerivator ---"
  for_ (the (List Int) [1..10]) $ \_ => do
    Just s <- pick (genUserStatusEdu (limit 20))
      | Nothing => printLn "Generation failed"
    printLn s
```

Run the test with:

```bash
echo -e ':exec testEdu' | rlwrap pack repl ./src/CustomGen.idr
```

Expected output (same as before, confirming it works):

```text
--- Testing EduDerivator ---
Active "Bob"
Inactive "sick"
Inactive "vacation"
Active "Charlie"
Inactive "offline"
Inactive "vacation"
Active "Bob"
Active "Alice"
Inactive "vacation"
Inactive "offline"
```

The output shows both constructors with our custom values, proving our `EduDerivator` correctly delegates to `CustomStatusGen`!

---

## Type Experts: Conclusions

Now you've seen two Type Experts:

1.  **`MainCoreDerivator`** (production): Handles fuel, recursion, weights, GADT indices, and more. Used in normal derivation.

2.  **`EduDerivator`** (educational): Minimal version showing the delegation pattern. Only works for non-recursive types.

---

## Architecture Recap

Let's summarize what we've learned:

1.  **Constructor Expert** (`DeriveBodyRhsForCon`): Controls **what arguments** each constructor receives. Called once per constructor.

2.  **Type Expert** (`DeriveBodyForType`): Controls **which constructor** gets called and manages fuel. Calls Constructor Expert for each constructor.

3.  **Delegation Pattern**: Type Expert calls `consGenExpr` to delegate argument generation to Constructor Expert.

4.  **Composition**: `MainCoreDerivator @{CustomStatusGen}` combines standard type-level logic with custom constructor-level logic.

This two-level architecture makes `DepTyCheck` highly modular: you can customize at either level without affecting the other!

---

## Path to Contribution

Understanding these internal APIs is the first step to extending `DepTyCheck`. If you find a new, useful derivation pattern or want to optimize certain cases, you now have the foundational knowledge to implement it and contribute back to the project.
