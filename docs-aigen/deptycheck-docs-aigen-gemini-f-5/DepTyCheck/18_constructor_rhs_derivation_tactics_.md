# Chapter 18: Constructor RHS Derivation Tactics

Welcome back! In [Chapter 17: Deep Constructor Application Analysis](17_deep_constructor_application_analysis_.md), we explored how `DepTyCheck` intricately analyzes how constructors influence GADT indices. This analysis is crucial preparation for what comes next: actually *building* the right-hand side (RHS) of a constructor's generator. But how `DepTyCheck` decides *how* to build that RHS can vary! This is where **Constructor RHS Derivation Tactics** come into play.

## What Problem Do Derivation Tactics Solve?

Imagine you're supervising a team of builders (our `canonicConsBody` from [Chapter 16: Constructor Body Derivation](16_constructor_body_derivation_.md)), and they need to assemble a constructor. They've gathered all the raw materials (the analysis from previous chapters). Now they need to combine them. There might be different "strategies" or "tactics" for how to do this:

1.  **"Least Effort" Tactic:** Just use the materials directly available on-site. Don't go out of your way to find fancy pre-made components (external generators) unless they naturally fit. Prioritize simplicity and direct construction.
2.  **"Best Effort" Tactic:** Actively look for fancy pre-made components (external generators) that fit, even if it requires a bit more planning. Try to use as many as possible.
3.  **"Obligatory" Tactics:** If a specific pre-made component *must* be used (an "obligatory" external generator), then prioritize it. If these obligatory components conflict, there are further tactics:
    *   **"Fail Fast":** If there's an unresolvable conflict between required pre-made components, just stop and declare it impossible.
    *   **"DecEq Conflicts":** If there are conflicts, try to resolve them by finding common ground (e.g., using equality checks).

The problem Constructor RHS Derivation Tactics solve is: **how can `DepTyCheck` implement different strategies for building the right-hand side of a constructor's generator, especially concerning whether and how to incorporate external (user-provided) generators?** Each tactic offers a different balance between simplicity, reliance on pre-existing components, and conflict resolution.

Our central use case for this chapter is: **To understand that `DepTyCheck` can employ various strategies (tactics) when constructing a generator for a constructor, with `LeastEffort` being the default, which prioritizes direct generation over strictly using external generators.**

## The `DeriveBodyRhsForCon` Interface: Defining the "Build Strategy"

The core of this module is the `DeriveBodyRhsForCon` interface. Any "tactic" must implement this interface, which requires providing a single function: `consGenExpr`.

```idris
-- From src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Interface.idr

public export
interface DeriveBodyRhsForCon where
  consGenExpr : DerivationClosure m => GenSignature -> (con : Con) -> (given : SortedSet $ Fin con.args.length) -> (fuel : TTImp) -> m TTImp
```

**Explanation:**

*   `interface DeriveBodyRhsForCon`: This defines the interface for strategies that derive the Right-Hand Side (RHS) of a constructor's generator.
*   `consGenExpr`: This is the function that defines *how* the generator is built.
    *   `DerivationClosure m`: As before, this gives us project management capabilities ([Chapter 13: Derivation Closure Management](13_derivation_closure_management_.md)) to call other generators recursively.
    *   `GenSignature`: The blueprint of the overall type's generator ([Chapter 6: Generator Signature Definition](06_generator_signature_definition_.md)).
    *   `con : Con`: The specific constructor we're building a generator for (e.g., `Red`, `MkUser`).
    *   `given : SortedSet $ Fin con.args.length`: A set of indices representing arguments of `con` that are already "given" or determined.
    *   `fuel : TTImp`: The `TTImp` for the fuel argument.
    *   `m TTImp`: The function returns a `TTImp` (the Idris code) for the RHS of the generator, wrapped in the monad `m`. This `TTImp` will likely be a `Gen` expression (e.g., `genString >>= \s => genInt >>= \i => pure (MkUser s i)`).

When `canonicConsBody` ([Chapter 16: Constructor Body Derivation](16_constructor_body_derivation_.md)) needs to determine the actual core generation logic for a constructor, it implicitly asks for an implementation of `DeriveBodyRhsForCon`, and `DepTyCheck` uses the one currently in scope (the default is `LeastEffort`).

## The `LeastEffort` Tactic: Prioritizing Simplicity

The `LeastEffort` tactic is the default and currently the most implemented strategy. It's called "least effort" because it calculates a generation order for the constructor's arguments without *obligatorily* using external generators. If an external generator fits the type of an argument along the chosen order, it will use it. But it won't re-arrange its generation order *just* to use an external generator.

This tactic is good when:
*   You don't need highly specialized external generators.
*   You want efficient generation that might not involve complex external dependencies.
*   You are primarily deriving generators for simple types or types with clear dependencies.

```idris
-- From src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr (simplified to show core logic)

export
[LeastEffort] DeriveBodyRhsForCon where
  consGenExpr sig con givs fuel = do
    -- 1. Analyze type arguments of the constructor (`argsTypeApps`)
    argsTypeApps <- getTypeApps con

    -- 2. Define how the constructor itself will be called later (`callCons`)
    let callCons = do
      -- ... builds the expression `pure (ConstructorName arg1 arg2 ...)` ...

    -- 3. Define the actual generation process for a given order (`genForOrder`)
    let genForOrder : List (Fin con.args.length) -> m TTImp
        genForOrder order = map (foldr apply callCons) $ evalStateT givs $ for order $ \genedArg => do
          -- Get type info for the argument to be generated (`typeOfGened`)
          let MkTypeApp typeOfGened _ _ = index genedArg argsTypeApps

          -- Determine sub-arguments needed for this arg's generator (`subgivens`)
          -- Construct a GenSignature for the sub-generator call (`subsig`)
          let (subgenCall, reordering) <- callGen subsig subfuel $ snd <$> subgivens -- Crucial call to `callGen`!

          -- Build code to bind the result of `subgenCall`
          -- (`subgenCall >>= \result => ...`)
          pure $ \cont => `(~subgenCall >>= ~(bindRHS cont))

    -- 4. Calculate the desired generation order (`theOrder`)
    -- This uses the `searchOrder` from Argument Permutation Utility ([Ch12](12_argument_permutation_utility_.md))
    -- and considers user-imposed tuning from GenOrderTuning ([Ch10](10_generator_tuning_interface_.md)).
    let determ = insertFrom' empty $ mapI (\i, ta => (i, ta.determ)) argsTypeApps
    -- ... more logic to decide `theOrder` (see original code for full detail) ...
    let theOrder = userImposed ++ searchOrder (removeDeeply userImposed nonDetermGivs)


    -- 5. Return the labeled and ordered generator expression
    labelGen ("\{show con.name} (orders)".label) <$> genForOrder theOrder
```

**Explanation of `LeastEffort` `consGenExpr` (simplified):**

1.  **`getTypeApps con`**: Uses `TypeApp` records to analyze each argument of the constructor (e.g., for `MkUser String Int`, it gets `TypeApp String` and `TypeApp Int`).
2.  **`callCons`**: Prepares the final constructor application (e.g., `pure (MkUser generatedString generatedInt)`).
3.  **`genForOrder order`**: This is the recursive helper that builds the generator expression following a given `order`. For each argument in the `order`:
    *   It determines the `GenSignature` (`subsig`) for the sub-generator needed to create this argument.
    *   It makes a critical call to `callGen subsig subfuel subgivens`. This `callGen` ([Chapter 13: Derivation Closure Management](13_derivation_closure_management_.md)) is where `DepTyCheck` decides if it should use an external generator or derive a new one for that sub-argument.
    *   It then builds a nested `>>=` (bind) expression to chain the sub-generator calls and eventually apply the constructor.
4.  **`theOrder`**: This is the core of the `LeastEffort` decision. It calculates an optimal generation order for the constructor's arguments using helper functions like `searchOrder` (from [Chapter 12: Argument Permutation Utility](12_argument_permutation_utility_.md)), which considers dependencies *and* any `GenOrderTuning` ([Chapter 10: Generator Tuning Interface](10_generator_tuning_interface_.md)) you might have provided. Crucially, at this stage, it does *not* prioritize using external generators unless they happen to fit the natural order.
5.  **`labelGen ... <$> genForOrder theOrder`**: Finally, it applies the calculated order to `genForOrder` to get the complete `TTImp` for the constructor's generator body, wrapping it in a label ([Chapter 8: Generator Labels](08_generator_labels_.md)).

The crucial aspect of `LeastEffort` is that the decision for `theOrder` (`searchOrder`) does not (by default) consider whether an external generator exists. It prioritizes dependency and simplicity. If, eventually, `callGen` does find an external generator that matches the `subsig`, it uses it; otherwise, it will schedule a new internal derivation.

## Other Tactics (Not Yet Implemented but Planned)

The comments in `src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr` hint at other planned tactics:

### "Best Effort" Non-Obligatory Tactics

These tactics would *try* to use as many external generators as possible, resolving conflicts where they arise, but without being strictly *obliged* to use any specific one. This would involve more complex analysis to find the best combination of external generators.

### "Obligatory" Tactics

These are much stricter. If an external generator for a certain type is marked as "obligatory," `DepTyCheck` *must* use it. This introduces new challenges:
*   **Conflict Resolution:** If two obligatory external generators require conflicting inputs for the same part of a complex type, how is this handled?
    *   `FailFast`: Just report an error and stop.
    *   `DecEqConflicts`: Try to use `DecEq` to find overlapping values between conflicting generators.

These planned tactics highlight the varying degrees of control and complexity `DepTyCheck` aims to offer in how it constructs generators.

## Sequence Diagram: `LeastEffort` in Action

Let's trace how `LeastEffort` would build a generator for `MkPair : MyGADT n -> MyGADT m -> MyGADT (n + m)`.

```mermaid
sequenceDiagram
    participant ConsGenBody as `canonicConsBody` (for `MkPair`)
    participant LeastEffort as `[LeastEffort] DeriveBodyRhsForCon.consGenExpr`
    participant TypeAnalyzer as `getTypeApps`
    participant OrderCalculator as `searchOrder` ([Ch12](12_argument_permutation_utility_.md))
    participant ClosureMgr as `DerivationClosure.callGen` ([Ch13](13_derivation_closure_management_.md))
    participant CodeBuilder as Code Fragments

    ConsGenBody->>LeastEffort: Call `consGenExpr` for `MkPair`
    LeastEffort->>TypeAnalyzer: `getTypeApps` for `MyGADT n` and `MyGADT m`
    TypeAnalyzer-->>LeastEffort: Returns `TypeApp` info for `n`, `m` (and their `Determination`)

    LeastEffort->>OrderCalculator: `searchOrder` (to figure out order for `n` then `m`)
    OrderCalculator-->>LeastEffort: Returns `theOrder = [n_idx, m_idx]` (natural left-to-right)

    LeastEffort->>LeastEffort: Start `genForOrder` with `[n_idx, m_idx]`
    LeastEffort->>ClosureMgr: Call `callGen` for `MyGADT n` (for first arg `x`)
    ClosureMgr-->>LeastEffort: Code for `genMyGADT_n` (e.g., `genMyGADT n_val fuel`)

    LeastEffort->>ClosureMgr: Call `callGen` for `MyGADT m` (for second arg `y`)
    ClosureMgr-->>LeastEffort: Code for `genMyGADT_m` (e.g., `genMyGADT m_val fuel`)

    LeastEffort->>LeastEffort: Constructs nested `>>=` expression:
        `genMyGADT_n >>= (\x_val => genMyGADT_m >>= (\y_val => pure (MkPair x_val y_val)))`

    LeastEffort-->>ConsGenBody: Returns this `TTImp` for the RHS.
    ConsGenBody->>CodeBuilder: Inserts this into the main `genMkPair` function body clause.
```

This diagram shows that `LeastEffort` orchestrates calls to several sub-modules to decide the order of arguments and then generates the code that chains together sub-generators, ultimately applying the constructor.

## Conclusion

Constructor RHS Derivation Tactics provide different strategies for `DepTyCheck` to build the core generation logic for a single constructor. The `DeriveBodyRhsForCon` interface, through its `consGenExpr` function, defines the contract for these tactics. The `LeastEffort` tactic is the default, prioritizing generation order based on dependencies and user tuning over strictly forcing external generator usage. While other, more complex "Best Effort" and "Obligatory" tactics are planned, `LeastEffort` provides a robust, simple, and effective default for automatically generating test data, seamlessly integrating with argument analysis and the closure management system to produce the final generator code. This modular approach allows `DepTyCheck` to adapt its behavior to various user requirements for generator construction.

Next, we'll shift our focus from generator construction to how `DepTyCheck` ensures that our generated test data effectively covers the possible values of a type in [Chapter 19: Generator Coverage Analysis](19_generator_coverage_analysis_.md).

[Next Chapter: Generator Coverage Analysis](19_generator_coverage_analysis_.md)

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)