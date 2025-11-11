# 8. Under the Hood: Building a `deriveGen`-like Macro

In the previous tutorials, we wielded the power of `deriveGen` and even learned how to tune it. In this final, advanced tutorial, we will go behind the curtain to understand how the magic happens. We will demystify `deriveGen` by building our own simplified version from scratch.

> **Disclaimer: This is a very Advanced Tutorial.** We will be interacting directly with the core interfaces of `DepTyCheck`'s derivation engine and using compile-time reflection (`ElabReflection`). This tutorial is for those who are not just users, but are curious about the mechanics of the library itself, or may even wish to contribute.

### Our Goal: A Custom Derivation Strategy

The default strategy for `deriveGen` is called `LeastEffort`. It gives all constructors a roughly equal chance. We are going to build a new, custom strategy called `MyStrategy` for a simple data type. Our strategy will be intentionally "stupid" to prove that it's working: it will be heavily biased and will always prefer one constructor over another.

By building a new derivation strategy from the ground up, you will understand the core components of the `DepTyCheck` engine.

### The Architecture of Derivation

`DepTyCheck`'s derivation is a multi-stage pipeline. For our purposes, we can think of it as a two-level hierarchy of experts:

1.  **The "Type Expert" (`DeriveBodyForType`):** Its job is to know about a *whole type*. It looks at all the constructors (e.g., `A` and `B` for our `Simple` type) and generates the top-level code that *chooses* between them. This is where `case fuel of` logic lives.

2.  **The "Constructor Expert" (`DeriveBodyRhsForCon`):** Its job is to know how to build *one specific constructor*. The Type Expert delegates to this expert, asking, "How do I build an `A`?" or "How do I build a `B`?"

In this tutorial, we will implement our own versions of both of these experts.

### Prerequisites

-   A good understanding of Idris's interfaces (type classes).
-   Completion of all previous tutorials, especially [Advanced Derivation Tuning](07-derivation-tuning.md).


---

## Step 1: The Setup

First, let's set up our file and define the simple data type we'll be working with. Our goal is to create a custom macro, `myDeriveGen`, that will automatically derive a generator for this `Simple` type, but using our own custom logic instead of the default `LeastEffort` strategy.

1.  **Create a new file** named `MyDerive.idr`.

2.  **Add the necessary setup.** We need a host of imports to interact with the derivation engine's internal interfaces.

    ```idris
    %language ElabReflection

    module MyDerive

    import Deriving.DepTyCheck.Gen -- The main entrypoint
    import Deriving.DepTyCheck.Gen.ForOneType.Interface
    import Deriving.DepTyCheck.Gen.ForOneType.Implementation
    import Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Interface
    import Deriving.DepTyCheck.Gen.ConsRecs

    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Runner
    import Data.Fuel

    -- The simple type we will derive a generator for
    data Simple = A Nat | B
    ```

---

## Step 2: Implement the "Constructor Experts"

Our first task is to write the logic for each individual constructor. In the `DepTyCheck` architecture, this is done by providing an implementation of the `DeriveBodyRhsForCon` interface. We will create two: one for `A` and one for `B`.

1.  **Create the logic for the `A` constructor.** This implementation simply generates the code `` `(A <$> deriveGen fuel)``, which means "call `deriveGen` to get a `Nat`, then apply the `A` constructor to it."

    ```idris
    [MyLogicFor_A] DeriveBodyRhsForCon where
      consGenExpr sig con givs fuel = pure `(A <$> deriveGen fuel)
    ```

2.  **Create the logic for the `B` constructor.** This one is even simpler. It just generates the code ` `(pure B)`.`
    ```idris
    [MyLogicFor_B] DeriveBodyRhsForCon where
      consGenExpr sig con givs fuel = pure `(pure B)
    ```

We have now created two named implementations (`MyLogicFor_A` and `MyLogicFor_B`) that act as specialists. `MyLogicFor_A` knows how to build the body of a generator for the `A` constructor, and `MyLogicFor_B` knows how to do it for `B`. In the next step, we'll create the "Type Expert" that knows to use these specialists.

---

## Step 3: Implement the "Type Expert"

Now we need to create the manager that understands the `Simple` type as a whole. Its job is to generate the main body of the generator function, deciding *when* to call the logic for `A` and when to call the logic for `B`. We do this by creating a mapping from constructor names to our named implementations from Step 2, and then writing our main strategy.

1.  **Create the Strategy Map.** This `instance` tells `DepTyCheck` that when it is operating under our custom strategy (`MyStrategy`), it should use `MyLogicFor_A` for the `A` constructor and `MyLogicFor_B` for the `B` constructor.

    ```idris
    [MyStrategy] DeriveBodyRhsForCon "MyDerive.A".dataCon where
      consGen = MyLogicFor_A

    [MyStrategy] DeriveBodyRhsForCon "MyDerive.B".dataCon where
      consGen = MyLogicFor_B
    ```

2.  **Implement the Type Expert.** Now we write the main logic. `MyTypeStrategy` implements `DeriveBodyForType` and is where we define our custom behavior. Instead of the default balanced `frequency`, we will create a heavily biased generator that *always* prefers the recursive `A` constructor when it has fuel.

    ```idris
    [MyTypeStrategy] DeriveBodyForType where
      canonicBody sig n =
        let
          -- Get the code for the two constructor bodies, using our named strategies
          b_body = consGenExpr @{MyStrategy} ...
          a_body = consGenExpr @{MyStrategy} ...

          -- Our biased logic!
          body = `(case fuel of
                     Dry => ~b_body -- Out of fuel, MUST choose B
                     More recFuel => ~a_body -- Always choose A if there is fuel
                 )
        in
          pure [ callCanonic sig n [var "fuel"] `((let fuel = var "fuel" in ~body)) ]
    ```

We have now defined a complete, custom derivation pipeline. All that's left is to wrap it in a user-facing macro.

---

## Step 4: Create the Top-Level Macro

Users don't interact with `DeriveBodyForType` directly. They use the `deriveGen` macro. The `deriveGen` function takes an optional `@` argument providing the core derivation logic. By default, this is `MainCoreDerivator @{LeastEffort}`. 

We will create our own macro, `myDeriveGen`, that simply calls `deriveGen` but passes our custom `MyTypeStrategy` instead.

```idris
MyDerivator : DeriveBodyForType
MyDerivator = MainCoreDerivator @{MyTypeStrategy}

myDeriveGen : Elab a
myDeriveGen = deriveGen @{MyDerivator}
```

---

## Step 5: Putting It All Together

We now have all the pieces. Let's use our custom macro to derive a generator for `Simple` and see our biased strategy in action.

1.  **Define the generator.** We define `genSimple` just like any other derived generator, but we set it equal to our custom macro.

    ```idris
    genSimple : Fuel -> Gen MaybeEmpty Simple
    genSimple = myDeriveGen
    ```

2.  **Test it!** Let's run it with a low fuel limit and see what happens. With `limit 2`, it should be forced to terminate quickly.

    ```idris
    main : IO ()
    main = do
      putStrLn "--- Running with custom 'A-biased' strategy ---"
      replicate 5 $ do
        Just s <- pick1 (genSimple (limit 2))
          | Nothing => printLn "Generation failed"
        printLn s
    ```

3.  **Analyze the output.** As expected, our biased strategy always picks `A` until it runs out of fuel, at which point it is forced to pick `B` to terminate. The output will look like `A (A (B))`.

    ```
    --- Running with custom 'A-biased' strategy ---
    A (A B)
    A (A B)
    A (A B)
    A (A B)
    A (A B)
    ```

We have successfully built and used a custom derivation macro!

---

## Congratulations!

You have built a working derivation macro from scratch. You now understand the fundamental architecture of `DepTyCheck`'s derivation engine and have seen that it is not magic, but a well-structured system of extensible interfaces. This is the deepest level of `DepTyCheck` mastery.

In this tutorial, you learned:

*   ✅ The core interfaces of the derivation engine: `DeriveBodyForType` and `DeriveBodyRhsForCon`.
*   ✅ How the "Type Expert" delegates work to "Constructor Experts".
*   ✅ How to implement these interfaces to create a custom derivation strategy.
*   ✅ How to wrap up your custom logic in a top-level macro that acts just like `deriveGen`.

### Path to Contribution

Understanding these internal APIs is the first step to extending `DepTyCheck`. If you find a new, useful derivation pattern or a more advanced strategy, you now have the foundational knowledge to implement it and contribute back to the project.