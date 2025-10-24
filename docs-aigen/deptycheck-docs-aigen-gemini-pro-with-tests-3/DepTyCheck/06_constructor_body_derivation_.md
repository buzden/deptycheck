# Chapter 6: Constructor Body Derivation

In our [last chapter on the Single-Type Derivation Core](05_single_type_derivation_core_.md), we met the "sous-chef" who creates the overall recipe for a data type. For a type like `Nat`, it knows to combine the recipes for `Z` and `S`. But we left out a crucial detail: who writes the recipe for a single, complex step like `S Nat`? Or even more, for a constructor with many interdependent arguments?

Welcome to the kitchen's assembly line, managed by the **Constructor Body Derivation** specialist. This is the "line cook" of our auto-derivation system. It gets a single ticket—one constructor—and its job is to perfectly assemble it, making sure all ingredients are prepared in the correct order.

### The Challenge: Arguments That Depend on Each Other

Simple constructors like `Z` (for `Nat`) are easy. But what about data where one field's *type* depends on another field's *value*? This is the heart and soul of dependent types, and it's where our line cook shines.

Consider a simple dependent pair that holds a number `n` and a vector of that exact length:

```idris
data MyPair = MkPair (n : Nat) (Vect n String)
```

To generate a random `MyPair`, `DepTyCheck` needs to produce a `MkPair` with its two arguments. A naive approach might be:
1.  Generate a random `Nat`.
2.  Generate a random `Vect n String`.

But wait! What is `n` in step 2? We can't generate the vector until we know what its length `n` is. The second argument (the vector) is *dependent* on the first (the number).

The Constructor Body Derivation component is responsible for figuring this out automatically. It knows it absolutely *must* have the length `n` before it can even attempt to generate the vector.

### The Solution: The Assembly Line Specialist

Think of the Constructor Body Derivation as a highly specialized line cook in our code-generation kitchen. The [Single-Type Derivation Core](05_single_type_derivation_core_.md) (the sous-chef) hands it a ticket that says: "Make me the body for a `MkPair` generator."

Here's the process our line cook follows:
1.  **Read the Blueprint:** It examines the `MkPair` constructor's arguments: `(n : Nat)` and `(v : Vect n String)`.
2.  **Spot the Dependencies:** It carefully analyzes the types and notices that the type of `v` contains `n`. It concludes: "`v` depends on `n`."
3.  **Create an Assembly Order:** Based on this dependency, it creates a step-by-step plan: "First, generate `n`. Second, use that `n` to generate `v`."
4.  **Request the Parts:** It doesn't make the parts itself. It goes back to the [Derivation Orchestrator](04_derivation_orchestrator_.md) (the head chef) to get generators for each part in the assembly order.
5.  **Build the Final Code:** It assembles the final code using a [`Gen` Monad](02__gen__monad_.md) `do` block, which is perfect for sequential, dependent steps.

Let's watch this line cook in action.

```mermaid
sequenceDiagram
    participant STCore as "Single-Type Core"
    participant ConsBody as "Constructor Body <br/> (Line Cook)"
    participant Orchestrator as "Orchestrator <br/> (Head Chef)"

    STCore->>ConsBody: Please generate the body for the `MkPair` constructor.
    ConsBody->>ConsBody: Arguments are `(n : Nat)` and `(v : Vect n String)`.
    ConsBody->>ConsBody: Analysis: `v` depends on `n`. The order must be `n`, then `v`.
    ConsBody->>Orchestrator: I need a generator for `Nat`.
    Orchestrator-->>ConsBody: Okay, use `genNat fuel`.
    ConsBody->>ConsBody: Great. I'll name the result `nValue`.
    ConsBody->>Orchestrator: Now, using `nValue`, I need a generator for `Vect nValue String`.
    Orchestrator-->>ConsBody: Okay, use `genVect nValue fuel`.
    ConsBody->>ConsBody: Assembly complete!
    ConsBody-->>STCore: Here is the code: `do nValue <- genNat fuel; ...`
```

The final code it assembles would look like this:

```idris
-- This is what gets generated for the `MkPair` constructor
do
  -- Step 1 (from the assembly order): Generate 'n'
  nValue <- genNat fuel
  -- Step 2 (from the assembly order): Generate 'v' USING 'nValue'
  vValue <- genVect nValue fuel
  -- Final assembly
  pure (MkPair nValue vValue)
```
This demonstrates the power of this component: it turns a declarative type definition into a precise, sequential generation plan.

### A Look Under the Hood: The `searchOrder` Algorithm

The magic of figuring out the assembly order happens in `src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr`. A key function here is what we can conceptually call `searchOrder`.

Imagine you have a set of tasks, and some tasks must be done before others. This is a classic computer science problem solved by a "topological sort." `searchOrder` is `DepTyCheck`'s own version of this.

Here’s a simplified view of its logic:
1.  **Analyze Dependencies:** For each argument of the constructor, it builds a profile. This is done by a helper function we can call `getTypeApps`.
    *   For `(n : Nat)`: This argument doesn't depend on any other arguments. Its dependency list is `[]`.
    *   For `(v : Vect n String)`: This argument depends on `n`. Its dependency list is `[n]`.
2.  **Assign Priorities:** Another helper, `assignPriorities`, gives each argument a score. Arguments that nothing depends on get the highest priority to be generated *first*.
3.  **Find the First Task:** `searchOrder` looks at all the argument profiles and asks: "Which argument has an empty dependency list?" In our case, only `n` does. So, `n` is the first item in our generation order.
4.  **Repeat:** It then conceptually "removes" `n` from the list of things to worry about and runs the process again. Now, when it looks at `v`, its dependency `n` is already taken care of. So `v` now has an empty dependency list. `v` becomes the next item in the order.
5.  **Finish:** The final order is `[n, v]`.

Here's what that thought process looks like in simplified pseudo-code:

```idris
-- Simplified from: src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr

-- determinationMap represents the dependencies for each argument
searchOrder : (determinationMap : Map ArgName (List ArgName)) -> List ArgName
searchOrder determined = do
  -- Find all args that have no remaining dependencies
  let notDetermined = filter (\arg => isEmpty (dependenciesOf arg)) (allArgs determined)

  -- Choose the best one to generate next (based on priorities)
  let Just (nextArg, _) = findFirstMax notDetermined
    | Nothing => [] -- All done!

  -- Update the map, effectively "checking off" nextArg
  let remainingDetermined = removeDependenciesOn nextArg determined

  -- Recurse to find the next item in the order
  nextArg :: searchOrder remainingDetermined
```
This recursive algorithm neatly builds the ordered list of arguments, which is then used to construct the `do` block we saw earlier. It's a clever and robust way to handle even very complex interdependencies between a constructor's fields.

### Conclusion

In this chapter, we've met the **Constructor Body Derivation** component, the detail-oriented "line cook" of `DepTyCheck`. We've learned that:

*   It is a specialist that focuses on generating the code for a **single constructor**.
*   Its most important job is to **analyze dependencies** between a constructor's arguments, especially in dependent types.
*   It uses a sophisticated ordering algorithm (`searchOrder`) to determine the **correct sequence** for generating these arguments.
*   It then calls back to the [Derivation Orchestrator](04_derivation_orchestrator_.md) to get the required sub-generators and assembles them into a final monadic expression.

This automatic dependency analysis is what makes `deriveGen` feel so magical. You define the "what" (the data type), and this component figures out the "how" (the sequential generation plan), freeing you from writing complex, boilerplate generator code.

But what if the automatic plan isn't quite what you want? What if you need to give the kitchen a hint, like "please make smaller vectors on average"? That's where our next chapter comes in.

Next, we'll explore how to influence and guide the automatic generation process in [Derivation Tuning](07_derivation_tuning_.md).

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)