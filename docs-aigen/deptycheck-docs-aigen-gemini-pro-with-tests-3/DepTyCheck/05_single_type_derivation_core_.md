# Chapter 5: Single-Type Derivation Core

In the [last chapter](04_derivation_orchestrator_.md), we met the [Derivation Orchestrator](04_derivation_orchestrator_.md), the "head chef" that manages the entire process of automatic generator derivation. When we ask it to `deriveGen` for a complex type, it figures out all the dependent types we need and creates a master plan.

But the head chef doesn't cook every dish personally. It delegates the work to a team of specialists. When a task like "create a generator for `Nat`" is on the to-do list, the Orchestrator hands it off to a very capable "sous-chef." This specialist is the **Single-Type Derivation Core**. Its job is to focus on creating one perfect generator for one specific data type.

### The Sous-Chef's Mission: Generate a `Nat`

Let's stick with our trusty `Nat` example.

```idris
data Nat = Z | S Nat
```

The [Derivation Orchestrator](04_derivation_orchestrator_.md) has given our sous-chef this simple order: "Please write the code for `genNat : Fuel -> Gen MaybeEmpty Nat`."

The sous-chef doesn't worry about any other types. It has one job, and it does it well. Its process looks like this:

1.  **Examine the Type**: It looks at the definition of `Nat` and sees it has two constructors: `Z` and `S`.
2.  **Plan for Each Constructor**: It figures out how to generate a value for each one.
    *   For `Z`: This is easy. It's a constant value. The recipe is simply `pure Z`.
    *   For `S`: This is more interesting. To create an `S Nat`, it must first create an inner `Nat`. This is a recursive step.
3.  **Combine the Plans**: It needs to create a single `Gen Nat` that can produce *either* a `Z` or an `S Nat`.
4.  **Manage Resources (Fuel)**: For the recursive `S` constructor, it must be careful not to create an infinite `S(S(S(...)))` loop. It uses the `Fuel` to handle this.

This chapter is all about how this specialist sous-chef executes this plan.

### Combining Constructors: `oneOf` vs. `frequency`

How do you combine the recipes for `Z` and `S`? `DepTyCheck` gives us two primary tools from the [`Gen` Monad](02__gen__monad_.md) kitchen: `oneOf` and `frequency`.

*   `oneOf`: Imagine you have a list of recipes, and you want to pick one with equal probability. `oneOf [genZ, genS]` would choose between the `Z` generator and the `S` generator 50/50.
*   `frequency`: What if you want to pick some recipes more often than others? `frequency [(2, genZ), (1, genS)]` would choose the `Z` generator twice as often as the `S` generator.

For a recursive type like `Nat`, we want to generate the base case (`Z`) more often to ensure our generated numbers don't get too big on average. So, `frequency` is the perfect tool. The Single-Type Derivation Core is smart enough to see that `S` is recursive and `Z` is not, so it will automatically choose to use `frequency` to give a higher chance to the non-recursive case.

### It's All About the Fuel

The most critical job of the Single-Type Core is to correctly use `Fuel`. `Fuel` can be in one of two states: `Dry` or `More`.

1.  **If `Fuel` is `Dry`**: The generator has run out of recursive energy. It *must* stop. The sous-chef knows this and will now *only* choose from the non-recursive constructors. For `Nat`, this means it will only generate `Z`.
2.  **If `Fuel` is `More`**: There's still energy! The sous-chef can choose from *any* constructor.
    *   If it picks a non-recursive one (`Z`), it uses the original `More` fuel.
    *   If it picks a recursive one (`S`), it makes a recursive call to `genNat`, but it passes the *remaining* fuel (`subFuel`) to that call, getting one step closer to `Dry`.

Let's see the code this sous-chef would write for `genNat`. While we just wrote `genNat = deriveGen`, this is the kind of code that gets generated behind the scenes:

```idris
-- This is what the Single-Type Core generates for `genNat`
genNat fuel =
  case fuel of
    Dry =>
      -- Fuel is out! Only generate the base case.
      pure Z

    More subFuel =>
      -- Still have fuel! Choose between Z and a recursive S.
      frequency
        [ (2, pure Z) -- Non-recursive option
        , (1, do n' <- genNat subFuel -- Recursive call with LESS fuel
                 pure (S n'))
        ]
```
This generated code perfectly captures the logic. It uses a `case` statement on the `fuel` to decide its strategy, ensuring that generation always terminates while still allowing for the creation of complex, recursive values.

### A Look Inside the Sous-Chef's Brain

How does the Single-Type Derivation Core do this automatically? The logic lives in `src/Deriving/DepTyCheck/Gen/ForOneType/Impl.idr`. When it receives its task from the Orchestrator, it follows a clear procedure.

```mermaid
sequenceDiagram
    participant Orchestrator
    participant STCore as "Single-Type Core (Sous-Chef)"
    participant ConsZ as "Plan for Z"
    participant ConsS as "Plan for S"
    participant Combined as "Final Generator Code"

    Orchestrator->>STCore: Please derive a generator for `Nat`.
    STCore->>STCore: Okay. `Nat` has two constructors: `Z` and `S`.
    STCore->>ConsZ: Create a simple generator for `Z`.
    ConsZ-->>STCore: Done. The code is `pure Z`.
    STCore->>ConsS: Create a generator for `S Nat`. I see this is recursive.
    ConsS-->>STCore: Done. The code is `do n' <- genNat subFuel; pure (S n')`.
    STCore->>STCore: Now, combine these. `S` is recursive, so I'll use `frequency`.
    STCore->>Combined: I'll wrap this in a `case fuel of` block.
    Combined-->>STCore: Final code is ready.
    STCore-->>Orchestrator: Here is the finished code for `genNat`.
```
The "Plan for Z" and "Plan for S" steps are actually handled by another, even more specialized component, the [Constructor Body Derivation](06_constructor_body_derivation_.md), which we'll see in the next chapter. The Single-Type Core's main job is to **ask for the plan for each constructor and then skillfully combine them** using the fuel logic.

### Peeking at the Internal Code

The main function that does this work is `canonicBody`. One of the most important parts is a helper function that we can call `fuelDecisionExpr`. Let's look at a conceptual, simplified version of what it does.

```idris
-- Simplified from: src/Deriving/DepTyCheck/Gen/ForOneType/Impl.idr

-- This function generates the main 'case fuel of ...' expression
fuelDecisionExpr : (fuelArg : Name) -> (constructors : List ConInfo) -> TTImp
fuelDecisionExpr fuelArg constructors = do
  -- Separate constructors into recursive and non-recursive
  let (recursive, nonRecursive) = partition isRecursive constructors

  -- If no recursive constructors exist, it's simple!
  if null recursive
    then pure (oneOf (all constructors))
    else do
      -- It's recursive, so we need the full 'case fuel of' logic
      iCase (var fuelArg)
        [ -- Case 1: Fuel is Dry
          Dry .= oneOf (nonRecursive constructors)

        , -- Case 2: Fuel is More
          More subFuel .= frequency
              ( (2, oneOf (nonRecursive constructors))
              , (1, oneOf (recursive constructors using subFuel))
              )
        ]
```
This simplified code snippet shows the heart of the sous-chef's intelligence. It analyzes the list of constructors for the type (`constrs`), determines which ones are recursive, and then builds the correct `case` expression using `oneOf` or `frequency` to manage the `fuel` and guarantee termination. The real code is more general and powerful, but this captures the essential idea.

### Conclusion

In this chapter, we met the **Single-Type Derivation Core**, the hard-working sous-chef of `DepTyCheck`'s auto-derivation kitchen. We learned that its role is to:

*   Focus on **one type at a time**, as assigned by the [Derivation Orchestrator](04_derivation_orchestrator_.md).
*   Analyze all of the type's **constructors** (like `Z` and `S` for `Nat`).
*   Intelligently combine the generators for each constructor using `oneOf` or `frequency`.
*   Crucially, it implements the **fuel-based logic** to handle recursion, ensuring that generation of recursive types like lists and trees will always terminate.

The Single-Type Core is responsible for the overall structure of a generator for one type. But how does it know what code to generate for a *single constructor*, especially a complex one like `MkProduct name category price`? That's the finely-detailed work of our next specialist.

In the next chapter, we will zoom in further and explore the [Constructor Body Derivation](06_constructor_body_derivation_.md), the expert responsible for filling in the details for each specific constructor.

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)