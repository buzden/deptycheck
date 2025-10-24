# Chapter 2: Generator Derivation Engine

In [Chapter 1: Test Data Generator (`Gen`)](01_test_data_generator___gen___.md), we learned how to write recipes (`Gen`s) for creating random data. While writing these recipes by hand is powerful, you probably noticed it can get a bit repetitive, especially for data types with many constructors or fields.

Imagine you have a large record with ten fields. You'd have to write a generator for each field and combine them all manually. Do this for a few dozen data types, and it becomes a real chore.

Wouldn't it be great if `DepTyCheck` could just look at your data type and write the `Gen` recipe for you? That's precisely what the Generator Derivation Engine does!

## The Auto-Chef for Test Data

Think of the Generator Derivation Engine as the "auto-chef" of the library. You simply show it the data type you want to generate, and it automatically writes the entire `Gen` recipe for you by looking at the type's structure.

Let's start with a very simple use case. Here's a `TrafficLight` data type:

```idris
data TrafficLight = Red | Amber | Green
```

To test functions that use `TrafficLight`, we need a generator. Manually, we'd write this:

```idris
import Test.DepTyCheck.Gen

-- A generator that randomly picks Red, Amber, or Green.
genTrafficLightManual : Gen NonEmpty TrafficLight
genTrafficLightManual = elements [Red, Amber, Green]
```

This is easy enough. But now, let's let the auto-chef do the work using `deriveGen`.

```idris
import Deriving.DepTyCheck.Gen

-- The signature of the generator we want.
genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
-- The implementation is derived automatically!
genTrafficLight = deriveGen
```

That's it! By writing `genTrafficLight = deriveGen`, you tell the compiler: "Please inspect the type `TrafficLight` and generate the body of this function for me." The engine sees the three constructors (`Red`, `Amber`, `Green`) and creates a generator that is functionally identical to `oneOf [pure Red, pure Amber, pure Green]`.

You might notice two small differences from the manual version:
1.  **`Fuel -> ...`**: The derived generator takes a `Fuel` argument. This is a mechanism to prevent infinite loops when generating recursive data, which we'll see soon. For a simple type like `TrafficLight`, it's not strictly needed, but `deriveGen` adds it by convention.
2.  **`Gen MaybeEmpty ...`**: The derivation engine always creates `MaybeEmpty` generators for maximum compatibility, as it can't always prove that a type has values (remember `Fin 0` from Chapter 1).

## Handling Dependencies and Recursion

The real power of the derivation engine shines with more complex, and even recursive, data types. Let's consider a simple `List` type.

```idris
data List a = Nil | Cons a (List a)
```

How would the engine derive a generator for `List Nat`?
- It sees two constructors: `Nil` and `Cons`.
- For `Nil`, it can just generate `pure Nil`.
- For `Cons a (List a)`, it realizes it needs two things:
    1.  A value of type `a` (which is `Nat` in our case).
    2.  A value of type `List a` (a recursive generation!).

The engine is smart enough to handle this. It knows it needs an external generator for `Nat` and that it needs to call itself recursively for the tail of the list. We provide the external generator as an `auto` implicit argument.

```idris
import Deriving.DepTyCheck.Gen

-- We need a generator for Nat, which we can also derive.
genNat : Fuel -> Gen MaybeEmpty Nat
genNat = deriveGen -- (Let's assume this is defined elsewhere)

-- Derive a generator for `List Nat`.
-- We provide the `genNat` as an auto-implicit dependency.
genListNat : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (List Nat)
genListNat = deriveGen
```

Here, the `(Fuel -> Gen MaybeEmpty Nat) =>` part of the signature tells the engine: "When you need a `Nat`, please use this generator that I'm providing automatically." The engine then wires everything together, producing a generator that might look something like this under the hood:

```idris
-- This is a simplified view of what `deriveGen` produces.
genListNatImpl : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (List Nat)
genListNatImpl fuel genNat =
  case fuel of
    Dry =>
      -- If we're out of fuel, only produce the non-recursive option.
      oneOf [pure Nil]

    More subFuel =>
      -- If we have fuel, we can choose between Nil and Cons.
      frequency
        [ (1, pure Nil) -- Base case
        , (1, [| Cons !(genNat subFuel) !(genListNatImpl subFuel genNat) |]) -- Recursive case
        ]
```
The engine automatically handles the recursion using `Fuel` to ensure the generation eventually stops.

## Under the Hood: A Three-Stage Assembly Line

How does this magic actually happen? The Generator Derivation Engine is like a multi-stage assembly line for building `Gen` code. When you call `deriveGen`, you're placing an order at the factory.

Let's trace what happens when we ask it to `deriveGen` for `genListNat`.

```mermaid
sequenceDiagram
    participant U as You
    participant DG as deriveGen
    participant FANT as ForAllNeededTypes (Factory Manager)
    participant FOT as ForOneType (List Manager)
    participant FOTC as ForOneTypeCon (Constructor Worker)

    U->>DG: Please build `genListNat`.
    DG->>FANT: Order received for `Gen (List Nat)`. It depends on `Gen Nat`.
    FANT->>FANT: OK. I'll manage the tasks: `Gen (List Nat)` and `Gen Nat`.
    FANT->>FOT: Start building the generator for `List Nat`.
    FOT->>FOT: `List Nat` has two parts: `Nil` and `Cons`.
    FOT->>FOTC: Build a generator for the `Nil` constructor.
    FOTC-->>FOT: Here you go: `pure Nil`.
    FOT->>FOTC: Now, build a generator for the `Cons` constructor.
    FOTC->>FANT: To build a `Cons`, I need a `Nat`. Can you get me a `Gen Nat`?
    FANT-->>FOTC: Sure, the user provided one via `auto` implicit. Use that.
    FOTC->>FOT: For the tail, I need to make a recursive call to `genListNat`.
    FOTC-->>FOT: Here's the plan for `Cons`: `do n <- genNat; tail <- genListNat; pure (Cons n tail)`
    FOT->>FOT: Great. I'll combine `Nil` and `Cons` using `frequency` and `Fuel` logic.
    FOT-->>FANT: The `genListNat` function is ready!
    FANT-->>DG: All tasks complete. Here is the final generated code.
```

1.  **`ForAllNeededTypes` (The Factory Manager):** This is the top-level orchestrator.
    - It receives the initial request (`deriveGen` for `List Nat`).
    - It maintains a queue of all generators that need to be built, including dependencies (`Gen Nat`). If `genNat` wasn't provided, and the engine was asked to derive it too, it would manage both tasks.
    - It ensures that each generator is built only once.
    - You can find its logic in `src/Deriving/DepTyCheck/Gen/ForAllNeededTypes/Impl.idr`.

2.  **`ForOneType` (The Type-Specific Manager):** This stage manages the derivation for one single data type.
    - It receives a task like "build a generator for `List`".
    - It inspects the type to find all its constructors (`Nil`, `Cons`).
    - It calls the next stage (`ForOneTypeCon`) for each constructor.
    - It then combines the results into a single generator, intelligently using `oneOf` or `frequency` and adding the `Fuel` logic to handle recursion.
    - Its implementation is in `src/Deriving/DepTyCheck/Gen/ForOneType/Impl.idr`. Here's a tiny peek at how it loops over constructors:
      ```idris
      -- In canonicBody function...
      -- For each constructor of the target type...
      consBodies <- for sig.targetType.cons $ \con =>
        -- ...derive the body for that constructor's generator.
        canonicConsBody sig (consGenName con) con
      ```

3.  **`ForOneTypeCon` (The Constructor Specialist):** This is the worker that handles a single constructor.
    - It receives a task like "build a generator for `Cons a (List a)`".
    - It figures out how to generate values for each field of the constructor.
    - If a field needs a generator (like `a`), it requests one from the `ForAllNeededTypes` manager.
    - If a field is a recursive call (like `List a`), it generates code to call the main generator with less `Fuel`.
    - You can find its logic in `src/Deriving/DepTyCheck/Gen/ForOneTypeCon/Impl.idr`.

This layered architecture allows the engine to break down a complex problem (deriving a generator for any type) into smaller, manageable steps.

## Conclusion

The Generator Derivation Engine is a huge time-saver that automates the tedious task of writing test data generators.

- You can automatically create a `Gen` for your data types with a single line: **`= deriveGen`**.
- The engine is a sophisticated **compile-time mechanism** that inspects your types.
- It's architected as a **three-stage assembly line** (`ForAllNeededTypes`, `ForOneType`, `ForOneTypeCon`) to manage dependencies, recursion, and the details of each constructor.

By letting the "auto-chef" handle the recipe, you can focus on the more important part: defining the properties you want to test.

But what if the default recipe isn't quite what you need? What if you want to tell the chef, "go easy on the `Nil`s" or "make my lists longer on average"? That's where you can start giving the engine specific instructions.

Next: [Chapter 3: Derivation Tuning](03_derivation_tuning_.md)

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)