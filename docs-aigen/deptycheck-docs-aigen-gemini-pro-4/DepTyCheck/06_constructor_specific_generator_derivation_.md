# Chapter 6: Constructor-Specific Generator Derivation

In the [previous chapter](05_type_level_generator_assembly_.md), we saw how `DepTyCheck` acts as a master controller, intelligently assembling a generator for an entire data type like `List`. It built a `case` statement on `Fuel` to choose between the mini-generators for `Nil` and `Cons`.

But that leaves a question: where do those mini-generators for `Nil` and `Cons` come from? How does `DepTyCheck` design the specific factory assembly line for just one model of a product? That's what we'll explore in this chapter.

## The Problem: Building a Specific Model

Let's look at a slightly more complex data type, the `Vect`, which is a list with its length encoded in its type.

```idris
data Vect : Nat -> Type -> Type where
  Nil  : Vect 0 a
  Cons : a -> Vect n a -> Vect (S n) a
```

Imagine we want to generate a `Vect 3 String`. The [Type-Level Generator Assembly](05_type_level_generator_assembly_.md) will decide to call the a `genCons` function three times. But what does that `genCons` function for `Vect 3 String` look like?

It's not simple. When we use the `Cons` constructor to build a `Vect 3 String`, the `Cons` signature is `a -> Vect n a -> Vect (S n) a`. The system needs to figure out:
1.  **"What is `n`?"**: If the final type is `Vect 3 ...`, and `3 = S n`, then `n` must be `2`.
2.  **"What is `a`?"**: The final type is `Vect ... String`, so `a` must be `String`.
3.  **"What order do I build things?"**: To build a `Cons`, we need a `String` and a `Vect 2 String`. Which should we generate first?
4.  **"Are the parts compatible?"**: If we are *given* some parts, do they match the constraints? For instance, if an external generator provides `n = 4`, we can't use that to build a `Vect 3 String` using `Cons`.

This process of figuring out the details for a single constructor is **Constructor-Specific Generator Derivation**.

Think of it as designing one specific assembly line in a car factory, like the one for the sedan model.
1.  **GADT Index Checking**: First, quality control inspects all the parts we've been given (`n=4`?) to ensure they match the sedan's blueprint (`S n = 3`).
2.  **Argument Ordering**: Then, an engineer figures out the most logical order to build the remaining parts (e.g., "build the chassis before you install the engine").
3.  **Delegation**: Finally, it calls a master engineer (the `DeriveBodyRhsForCon` interface) to write the step-by-step instructions for the workers.

## Step 1: Quality Control (GADT Index Checking)

Generalized Algebraic Data Types (GADTs) like `Vect` have rules embedded in their types. `Cons` can only build a `Vect (S n) a` if it's given a tail of type `Vect n a`.

When `DepTyCheck` derives a generator for the `Cons` constructor in the context of `Vect 3 String`, it generates code to check these rules. The goal is to generate a `Vect (S n) a` where `S n` is `3` and `a` is `String`. The `Cons` constructor has a head of type `a` and a tail of type `Vect n a`. The system must ensure that `S n` and `3` are propositionally equal.

It does this by generating `with` clauses that use `decEq` (decidable equality).

```idris
-- The conceptual code DepTyCheck generates for the GADT check
genConsVect3String : ...
genConsVect3String given_n given_a =
  with (decEq (S given_n) 3)
    Yes Refl => -- The `n` we have works! `n` is now known to be 2.
                -- Let's proceed to build the body...
                ... build `a` and `Vect n a` ...

    No _     => -- The `n` we have doesn't work.
                -- This assembly line can't be used.
                empty
```

If the check fails (e.g., we are asked to build a `Vect 3 String` but an external parameter forces `n` to be `4`), the generated path for this constructor returns an `empty` generator. It's a dead end. If it succeeds, the rest of the generation knows that it must recursively generate a `Vect 2 String`.

This powerful mechanism allows `DepTyCheck` to correctly handle even the most complex GADTs.

## Step 2: The Assembly Plan (Argument Generation Order)

Once the checks pass, `DepTyCheck` knows what arguments it needs to generate. For `Cons`, it needs an `a` and a `Vect n a`. But in what order?

Sometimes, one argument's type depends on another argument's *value*. Consider this type:

```idris
data SizedPair = MkPair (n : Nat) (Fin n)
```

To generate a `MkPair`, you absolutely *must* generate `n` first. You can't create a `Fin n` without knowing what `n` is!

The implementation of `DeriveBodyRhsForCon` is responsible for this analysis. It looks at the types of all the arguments (`n : Nat` and `Fin n`), finds dependencies between them, and creates an ordered assembly plan.
*   `Fin n` depends on `n`.
*   `n` depends on nothing.
*   **Plan:** Generate `n` first, then generate `Fin n`.

This dependency analysis is a key part of what makes `DepTyCheck` work for dependent types. We'll see more about how it's done in the next chapter.

## Step 3: Delegating to the Engineer (`DeriveBodyRhsForCon`)

After the GADT checks are in place and the argument order is decided, the system needs to generate the final code that actually *calls* the sub-generators and puts the pieces together.

This job is handed off to an "engineer"—the `DeriveBodyRhsForCon` interface.

```idris
-- From: src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Interface.idr
export
interface DeriveBodyRhsForCon where
  consGenExpr : ... -> m TTImp
```

This interface says: "Give me all the information about the constructor, what's already been generated (`given`), and the fuel, and I will return the final code (`TTImp`) for the generator's body."

The default implementation of this interface (`LeastEffort`) takes the ordered list of arguments from Step 2 and generates a chain of `do` notation steps.

For `MkPair`, it would generate code that looks like this:

```idris
-- Conceptual code generated by `consGenExpr`
do
  n <- callGen Nat ...      -- Step 1 from the plan: get a Nat
  fin <- callGen (Fin n) ... -- Step 2: use `n` to get a Fin n
  pure (MkPair n fin)       -- Finally, assemble the product
```

This separation of concerns is powerful. The main logic in this chapter handles the high-level GADT checking, and it delegates the detailed, step-by-step assembly instructions to this specialized interface.

## Under the Hood: `canonicConsBody`

The entire process for a single constructor is managed by the `canonicConsBody` function in `src/Deriving/DepTyCheck/Gen/ForOneTypeCon/Impl.idr`. Let's trace how it works for our `Cons` example.

```mermaid
sequenceDiagram
    participant TA as Type-Level Assembler
    participant CCB as canonicConsBody
    participant RHS as DeriveBodyRhsForCon
    participant Orchestrator

    TA->>CCB: Build a generator for the `Cons` constructor.
    CCB->>CCB: Analyze `Cons`: `a -> Vect n a -> Vect (S n) a`
    Note right of CCB: Target is `Vect 3 String`.<br>So `S n` must equal `3`.
    CCB->>CCB: Generate `with (decEq (S n) 3) ...` checks.
    Note over CCB: If check passes, `n` is now known to be `2`. Let's assume it passes.
    CCB->>RHS: Build body for `Cons` with args `(String, Vect 2 String)`.
    RHS->>RHS: Analyze dependencies: no dependencies between args.
    Note right of RHS: Order: `[String, Vect 2 String]` is fine.
    RHS->>Orchestrator: I need a generator for `String`.
    Orchestrator-->>RHS: Here's the code for `genString`.
    RHS->>Orchestrator: I need a generator for `Vect 2 String`.
    Orchestrator-->>RHS: Here's the code for `genVect2`.
    RHS->>RHS: Assemble the `do` block.
    Note right of RHS: `do s <- genString; v <- genVect2; pure (Cons s v)`
    RHS-->>CCB: Here is the code for the constructor body.
    CCB-->>TA: Here is the complete `genCons` function, with checks.
```

The GADT checking part is implemented in a helper function within `canonicConsBody` called `deceqise`. It builds a nested series of `WithClause` expressions.

```idris
-- A tiny glimpse into `deceqise`
deceqise ... = step ... where
  step ... [] = -- All checks passed! Call the RHS Deriver.
    ... !(consGenExpr sig con ...)

  step ... ((orig, renam)::rest) =
    -- Generate a 'with' clause for one check
    WithClause ... `(decEq ~(var renam) ~(var orig)) ...
      [ -- Yes, it's equal. Recurse to the next check.
        step ... rest
      , -- No, it's not. This path is impossible.
        ... .| `(empty)
      ]
```
This elegant metaprogramming generates all the necessary quality control checks. If all checks pass, it finally calls `consGenExpr` (our engineer interface) to build the core of the generator.

The logic for determining the generation order lives within the `consGenExpr` implementation itself, using a function called `searchOrder` which performs the dependency analysis we described.

## Summary and Next Steps

You've just peered into the heart of the assembly line!

*   **Constructor-Specific Generator Derivation** is the process of building a generator for a *single constructor* of a data type.
*   It first performs **GADT Index Checking** using `decEq` to ensure all type-level constraints are met.
*   It then determines the best **Argument Generation Order** by analyzing dependencies between the constructor's arguments.
*   Finally, it delegates the creation of the generator's body to the **`DeriveBodyRhsForCon`** interface, which pieces together the calls to sub-generators.

We've touched on two critical but complex topics: figuring out which constructors are recursive and determining the generation order of arguments. How does `DepTyCheck` perform this clever analysis?

In the next chapter, we will investigate the component responsible for this deep analysis: [Recursion and Weight Analysis](07_recursion_and_weight_analysis_.md).

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)