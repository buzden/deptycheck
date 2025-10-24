# Chapter 6: Constructor-Specific Derivation (`DeriveBodyRhsForCon`)

In the [previous chapter](05_single_type_derivation_core___derivebodyfortype___.md), we met the "master craftsman," [`DeriveBodyForType`](05_single_type_derivation_core___derivebodyfortype___.md). This component assembles the final generator function, creating the crucial `case fuel of` logic that prevents infinite recursion.

The craftsman does the high-level assembly, but it delegates the creation of the individual parts. For a `Nat` generator, it needs one recipe for the `Z` constructor and a separate one for the `S Nat` constructor. Who builds these smaller, specific recipes?

This is the job of the **`DeriveBodyRhsForCon`**, the specialist "assembly line worker" of the derivation process.

## The Assembly Line Worker

Think of `deriveGen` as a factory. The [Derivation Orchestrator](04_derivation_orchestrator_.md) is the factory manager, and [`DeriveBodyForType`](05_single_type_derivation_core___derivebodyfortype___.md) is a production line supervisor. This supervisor, `DeriveBodyForType`, points to a specific constructor on the data type's blueprint and tells an assembly line worker, **`DeriveBodyRhsForCon`**, "Build me a recipe for just this part."

So, for `data Nat = Z | S Nat`, the supervisor makes two requests:
1.  "Worker, build a recipe for `Z`."
2.  "Worker, build a recipe for `S Nat`."

This worker's job is to figure out exactly how to build a generator for that *one specific constructor*. For simple constructors like `Z`, the job is easy: `pure Z`. But for complex constructors, especially in dependent types, this task is a fascinating puzzle.

## The GADT Puzzle: Order Matters

Let's look at a classic dependent type, `Vect`:

```idris
data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a
```

Now, imagine `DeriveBodyRhsForCon` is asked to create a recipe for the `(::)` constructor. This constructor takes two arguments: an element of type `a`, and a tail of type `Vect k a`.

To create the recipe, `DeriveBodyRhsForCon` needs to get generators for both arguments and plug them into the `(::)` constructor.
It would generate code that looks something like this:

```idris
-- Generate an 'a', then a 'Vect k a', then combine them.
[| head :: tail |]
```

For `Vect`, the order in which we generate `head` and `tail` doesn't really matter. But what if one argument's *type* depends on another argument's *value*?

Consider this example:

```idris
data ItemInfo : (itemId : Nat) -> Type where
  -- ... details not important ...

data Order : Type where
  MkOrder : (id : Nat) -> (info : ItemInfo id) -> Order
```
An `Order` has an `id` and some `info`. Crucially, the type of `info` is `ItemInfo id`, which means the info we can have depends on the ID we pick.

If the assembly line worker is asked to build a recipe for `MkOrder`, it faces a puzzle: what is the correct order to generate the arguments?

1.  **Option A (Wrong):** Generate `info` first, then `id`. This is impossible! We can't generate `info` because we don't know its type yet. Its type depends on `id`, which we haven't generated.
2.  **Option B (Correct):** Generate `id` first. Once we have a specific `id` (say, `42`), the type of `info` becomes clear (`ItemInfo 42`). We can then ask for a generator for `ItemInfo 42` and generate the `info`.

This is the central puzzle that `DeriveBodyRhsForCon` solves. It analyzes the dependencies between a constructor's arguments and determines the one correct order to generate them in.

## The `LeastEffort` Solution

`DeriveBodyRhsForCon` is an interface, which means different strategies could be used to solve this puzzle. The default and primary strategy used in `DepTyCheck` is called `LeastEffort`.

The `LeastEffort` worker is a clever puzzle-solver. Here's its step-by-step process for building a recipe for `MkOrder`:

1.  **Analyze Dependencies:** It looks at all the arguments of `MkOrder`: `(id : Nat)` and `(info : ItemInfo id)`. It builds a mental dependency map:
    *   `id` depends on nothing.
    *   `info` depends on `id`.

2.  **Find a Starting Point:** It searches for an argument that has no dependencies. In this case, that's `id`. This is the first thing it must generate.

3.  **Generate and Update:** The worker asks the [Derivation Orchestrator](04_derivation_orchestrator_.md) for a generator for `Nat`. It generates code to run that generator and bind the result to the name `id`.
    Now, its mental map of "known values" includes `id`.

4.  **Repeat:** It looks at the remaining arguments. The only one left is `info`. Are all of its dependencies met? Yes, `info` depends on `id`, which is now a "known value".
    So, the worker asks the Orchestrator for a generator for `ItemInfo id`, passing the *value* of `id` that was just generated.

5.  **Assemble the Final Recipe:** The worker takes all these ordered steps and assembles them into a final monadic generator recipe. Conceptually, it builds this:

    ```idris
    do
      -- Step 1: Generate the independent value 'id'.
      id <- genNat
      -- Step 2: Use 'id' to generate the dependent value 'info'.
      info <- genItemInfo id
      -- Step 3: Combine them with the constructor.
      pure (MkOrder id info)
    ```
This is the power of `DeriveBodyRhsForCon`. It turns a complex, dependent constructor into a simple, step-by-step recipe that respects the type-level dependencies.

## Under the Hood: A Choreographed Dance

Let's visualize how the worker (`DeriveBodyRhsForCon`) gets its job done. It choreographs a dance between dependency analysis and requesting sub-generators from the Orchestrator's `callGen` function.

```mermaid
sequenceDiagram
    participant D4T as DeriveBodyForType (Supervisor)
    participant D4C as DeriveBodyRhsForCon (Worker)
    participant DA as Dependency Analysis
    participant CG as callGen (Orchestrator)
    participant RC as Resulting Code

    D4T->>D4C: Build me a recipe for the `MkOrder` constructor.
    D4C->>DA: Analyze arguments of `MkOrder`.
    DA-->>D4C: `info` depends on `id`. Order must be `[id, info]`.
    Note over D4C: Okay, first argument to generate is `id`.
    D4C->>CG: I need a generator for `Nat`.
    CG-->>D4C: Here's the code to call `genNat`.
    Note over D4C: Great. Now I have `id`. Next is `info`.
    D4C->>CG: I need a generator for `ItemInfo id`.
    Note over CG: Okay, that's a dependent call.
    CG-->>D4C: Here's the code to call `genItemInfo id`.
    D4C->>RC: Assemble the final `do` block.
    RC-->>D4C: `do { id <- genNat; info <- genItemInfo id; pure ... }`
    D4C-->>D4T: Here is the finished recipe for `MkOrder`.
```
This diagram shows how `DeriveBodyRhsForCon` acts as a middle-man. It figures out the *what* and the *when* (the order), and then asks the orchestrator's `callGen` function to provide the *how* (the actual sub-generators).

### A Peek at the Code

This logic resides in `src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr`. The main method for the `LeastEffort` strategy is `consGenExpr`.

First, it analyzes all constructor arguments to build the dependency map.

```idris
-- File: src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr

-- ... Inside [LeastEffort] consGenExpr ...

-- Compute determination map ...
let determ = insertFrom' empty $ mapI (\i, ta => (i, ta.determ)) argsTypeApps
```
This `determ` map contains all the dependency information puzzle-solver needs.

Next, it uses a function called `searchOrder` to solve the puzzle and find the correct generation order.

```idris
-- File: src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr

-- Compute the order
let theOrder = ... ++ searchOrder (removeDeeply ... determ)
```
`searchOrder` repeatedly finds an argument with no unmet dependencies, adds it to the list, and continues until all arguments are accounted for.

Finally, it builds the final generator by iterating over `theOrder` and building up the monadic `do` block step by step.

```idris
-- File: src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr

-- A simplified view of how the recipe is built.
genForOrder : List (Fin con.args.length) -> m TTImp
genForOrder order =
  -- Fold over the ordered arguments, building up the final expression.
  foldr apply callCons !(for order $ \genedArg => do

    -- ... logic to figure out the sub-generator signature ...

    -- Form an expression to call the subgen via the orchestrator
    (subgenCall, _) <- callGen subsig subfuel ...

    -- Chain the call with the rest of the computation.
    -- This builds `... >>= \arg => ...`
    pure $ \restOfComputation => `(~subgenCall >>= \_ => ~restOfComputation)
  )
```
This loop is the core of the recipe construction. For each argument in the correct order, it calls `callGen` to get a sub-generator and then uses `>>=` (the bind operator) to chain it to the next step, ensuring that the result of one step is available for the next.

## Conclusion

The `DeriveBodyRhsForCon` is the unsung hero that handles the nitty-gritty details of `deriveGen`. Without it, generating values for complex dependent types would be impossible.

You've learned that this "assembly line worker":
*   Is a specialist that builds a `Gen` recipe for **one single constructor**.
*   Solves the "GADT puzzle" by figuring out the correct **order** to generate a constructor's arguments based on their type-level dependencies.
*   The `LeastEffort` strategy does this by analyzing dependencies and picking arguments with no unmet dependencies one by one.
*   It builds the final recipe by calling the `callGen` orchestrator for each argument and chaining them together monadically.

We've seen `DeriveBodyForType` deciding which constructors are recursive and `DeriveBodyRhsForCon` figuring out generation order. These analytical steps are crucial. How exactly does `deriveGen` perform this analysis? We'll find out in the next chapter as we explore [Recursion and Weight Analysis (`ConsRecs`)](07_recursion_and_weight_analysis___consrecs___.md).

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)