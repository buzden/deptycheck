# Chapter 10: DeriveBodyRhsForCon

Welcome back to `DepTyCheck`! In our [previous chapter](09_deepconsanalysisres.md), we learned how `DepTyCheck` deeply inspects the arguments of constructors using `DeepConsAnalysisRes` to understand their dependencies and type-determining roles. All of this groundwork, from understanding generators to managing recursion and analyzing expressions, culminates in this chapter.

Today, we're going to talk about `DeriveBodyRhsForCon`. This is the **grand architect** that brings all these pieces together to actually **build the right-hand side (RHS) of a constructor's generator function**. What does that mean? When `DepTyCheck` automatically generates code like:

```idris
genPost : Fuel -> Gen MaybeEmpty Post
genPost fuel = do -- This 'do' block, and everything inside it, is the RHS!
  -- ... code that generates id, author, title ...
  pure $ MkPost id' author' title'
```

`DeriveBodyRhsForCon` is responsible for generating that `do` block content. It's like choosing a specific strategy or "tactic" for how to build a complex object, deciding the order of operations, what sub-generators to call, and how to combine their results.

## The Problem: How Do We Build a Constructor's Generator?

Let's revisit our `Post` example, which has three fields: `id : Nat`, `author : User`, and `title : String`.

```idris
record Post where
  id     : Nat
  author : User
  title  : String
```

When `DepTyCheck` is asked to derive `genPost`, it needs to construct the body of this generator function. For the `MkPost` constructor, this means it needs to:

1.  **Decide the generation order:** Should we generate `id` first, then `author`, then `title`? Or `author` first? The order can matter, especially with dependent types!
2.  **Generate each argument:** For `id`, it needs to call `genNat`. For `author`, it needs `genUser`. For `title`, `genString`.
3.  **Handle dependencies:** If `genUser` itself needs other generators, `DeriveBodyRhsForCon` uses [DerivationClosure](06_derivationclosure.md) to kick off those sub-derivations.
4.  **Chain results:** It needs to put all these individual generations into a `do` block and bind their results to variables (e.g., `id' <- genNat fuel`).
5.  **Construct the final value:** Finally, it needs to form the `MkPost id' author' title'`.
6.  **Decorate and label:** It might also add labels ([CTLabel](04_ctlabel__compile_time_label__.md)) for coverage ([ModelCoverage](05_modelcoverage.md)) and debuggability.

`DeriveBodyRhsForCon` defines a blueprint for how to do all of this. Different "tactics" (implementations of this interface) can approach these steps differently, leading to different generation behaviors.

## `DeriveBodyRhsForCon`: The Interface

The `DeriveBodyRhsForCon` is an interface with a single method: `consGenExpr`.

```idris
-- src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Interface.idr

public export
interface DeriveBodyRhsForCon where
  consGenExpr : DerivationClosure m => GenSignature -> (con : Con) -> (given : SortedSet $ Fin con.args.length) -> (fuel : TTImp) -> m TTImp
```

**Explanation:**
*   `interface DeriveBodyRhsForCon`: This declares `DeriveBodyRhsForCon` as an interface.
*   `consGenExpr`: This is the function that any implementation of this interface *must* provide. Its job is to produce the `TTImp` (the Idris code representation) for the right-hand side of a constructor's generator.
    *   `DerivationClosure m =>`: The `m` monad (where `consGenExpr` runs) must provide a `DerivationClosure` implementation. This means `consGenExpr` can use `callGen` to request other generators for the constructor's arguments.
    *   `sig : GenSignature`: The [GenSignature](07_gensignature.md) for the overall type. This tells `consGenExpr` about the type being generated and its "given" parameters.
    *   `con : Con`: The specific constructor (like `MkPost`) for which we are generating the RHS. This includes all its arguments.
    *   `given : SortedSet $ Fin con.args.length`: This specifies which arguments of *this constructor* are already "given" by the user and therefore don't need to be generated.
    *   `fuel : TTImp`: The `Fuel` argument for the generator. `consGenExpr` needs to know about this to pass `Fuel` down to recursive calls.
    *   `m TTImp`: The function returns `TTImp`, which is the Idris internal code representation of the generate `do` block (or `pure` expression if it's a simple case).

This `consGenExpr` function is where all the complex logic we discussed (ordering, calling sub-generators, chaining results) lives for a specific tactic.

## The Default Tactic: `LeastEffort`

`DepTyCheck` comes with a default implementation (`tactic`) for `DeriveBodyRhsForCon` called `LeastEffort`. As its name implies, this tactic tries to generate the constructor's arguments in the "easiest" way possible. It's a non-obligatory tactic, meaning it doesn't *force* the use of external generators if generating locally is straightforward.

Let's trace out, conceptually, how `LeastEffort.consGenExpr` would build the generator body for `MkPost id author title`.

**Goal:** Derive `genMkPost : Fuel -> Gen MaybeEmpty Post` (assuming `id`, `author`, `title` are all to be generated internally).

**`LeastEffort`'s Approach (simplified):**

1.  **Analyze `MkPost`'s arguments:** It first looks at `id`, `author`, `title`.
2.  **Determine order:** It tries to find a good order for generation. This involves:
    *   Using [DeepConsAnalysisRes](09_deepconsanalysisres.md) to understand dependencies between `con.args`. For example, if `author` was `User id` instead of just `User`, then `author` would depend on `id`, so `id` must be generated first.
    *   Considering arguments that are `given` to the constructor.
    *   Potentially considering user-defined tuning (e.g., "always generate `id` first").
    *   The `searchOrder` function in `LeastEffort` is responsible for this. It prioritizes arguments based on their dependency and "complexity" to find a stable generation order (e.g., `id`, then `author`, then `title`).
3.  **Generate code for each argument in order:** For each argument in the decided order:
    *   Let's say the order is `id`, `author`, `title`.
    *   **For `id`:**
        *   It constructs a [GenSignature](07_gensignature.md) for `Nat`.
        *   It calls `callGen` ([DerivationClosure](06_derivationclosure.md)) with this `GenSignature` and the current `fuel`.
        *   `callGen` returns `genNat fuel`.
        *   `LeastEffort` adds `id' <- genNat fuel` to the `do` block.
    *   **For `author`:**
        *   It constructs a `GenSignature` for `User`.
        *   It calls `callGen` with this `GenSignature` and `fuel`.
        *   `callGen` returns `genUser fuel`.
        *   `LeastEffort` adds `author' <- genUser fuel` to the `do` block.
    *   **For `title`:**
        *   It constructs a `GenSignature` for `String`.
        *   It calls `callGen` with this `GenSignature` and `fuel`.
        *   `callGen` returns `genString fuel`.
        *   `LeastEffort` adds `title' <- genString fuel` to the `do` block.
4.  **Assemble into a `do` block:** It then chains these monadic binds (`>>=`) together using the `genForOrder` function.
5.  **Final `pure` and constructor application:** It adds `pure $ MkPost id' author' title'` at the end of the `do` block.
6.  **Add Labels:** Finally, it wraps the entire generated `do` block with a [CTLabel](04_ctlabel__compile_time_label__.md) like `"MkPost (orders)"` to facilitate [ModelCoverage](05_modelcoverage.md) and debugging.

The resulting `TTImp` for `genMkPost`'s RHS would look something like this (conceptual Idris code):

```idris
-- This is generated by DeriveBodyRhsForCon.LeastEffort
Test.DepTyCheck.Gen.label (fromString "MkPost (orders)") $ do
  id'    : Nat    <- Test.DepTyCheck.Gen.label (fromString "id") (genNat fuel)
  author' : User   <- Test.DepTyCheck.Gen.label (fromString "author") (genUser fuel)
  title' : String <- Test.DepTyCheck.Gen.label (fromString "title") (genString fuel)
  pure $ MkPost id' author' title'
```

This `LeastEffort` tactic is the "default" as indicated by this line in `Gen.idr`:
```idris
-- src/Deriving/DepTyCheck/Gen.idr
%defaulthint %inline
public export
DefaultConstructorDerivator : DeriveBodyRhsForCon
DefaultConstructorDerivator = LeastEffort
```
This means that unless you specify otherwise with a different `DeriveBodyRhsForCon` implementation, `DepTyCheck` will use the `LeastEffort` strategy.

## Non-Code/Code-Light Walkthrough: `DeriveBodyRhsForCon` in Action

Let's visualize the process of deriving `genMkPost` with `LeastEffort`:

```mermaid
sequenceDiagram
    participant TopDeriver as Top-level Deriver
    participant ConsGenExpr as consGenExpr (LeastEffort)
    participant Analyzer as DeepConsAnalysisRes / searchOrder
    participant DerivationClosureC as DerivationClosure
    participant GenNat as genNat
    participant GenUser as genUser
    participant GenString as genString
    participant Labeler as CTLabel Wrapper

    TopDeriver->ConsGenExpr: Call consGenExpr(sig, MkPost, {}, fuel)
    ConsGenExpr->Analyzer: Determine argument generation order (e.g., id, author, title)
    Analyzer-->ConsGenExpr: Order: [id, author, title]

    loop For each argument in order
        ConsGenExpr->DerivationClosureC: callGen(GenSignature for argument, fuel)
        alt If argument is `id` (Nat)
            DerivationClosureC->GenNat: Provide reference to genNat
            GenNat-->DerivationClosureC: (genNat fuel) code
            DerivationClosureC-->ConsGenExpr: (genNat fuel) code
            ConsGenExpr->Labeler: Wrap (genNat fuel) with "id" label
            Labeler-->ConsGenExpr: `id' <- label ("id") (genNat fuel)`
        alt If argument is `author` (User)
            DerivationClosureC->GenUser: Provide reference to genUser
            GenUser-->DerivationClosureC: (genUser fuel) code
            DerivationClosureC-->ConsGenExpr: (genUser fuel) code
            ConsGenExpr->Labeler: Wrap (genUser fuel) with "author" label
            Labeler-->ConsGenExpr: `author' <- label ("author") (genUser fuel)`
        alt If argument is `title` (String)
            DerivationClosureC->GenString: Provide reference to genString
            GenString-->DerivationClosureC: (genString fuel) code
            DerivationClosureC-->ConsGenExpr: (genString fuel) code
            ConsGenExpr->Labeler: Wrap (genString fuel) with "title" label
            Labeler-->ConsGenExpr: `title' <- label ("title") (genString fuel)`
        end
    end

    ConsGenExpr->ConsGenExpr: Assemble all steps into a 'do' block
    ConsGenExpr->ConsGenExpr: Add `pure $ MkPost id' author' title'`
    ConsGenExpr->Labeler: Wrap entire 'do' block with "MkPost (orders)" label
    Labeler-->ConsGenExpr: Final TTImp for RHS
    ConsGenExpr-->TopDeriver: Derived TTImp for genMkPost RHS
```

This sequence diagram illustrates how `consGenExpr` orchestration pulls together information from various `DepTyCheck` components to generate the final code for the constructor's RHS.

## Diving into the Code (`src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr`)

The `LeastEffort` implementation is quite large and complex, as it contains all the logic for ordering arguments, handling dependencies via `callGen`, and composing the final `TTImp`.

Here are some key parts from `Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Impl.idr` that correspond to the steps above:

1.  **`consGenExpr sig con givs fuel = do ...`**: The main function body.

2.  **`argsTypeApps <- getTypeApps con`**: This function (defined within this file) analyzes each argument of the constructor `con`. It identifies the head type of each argument and, importantly, what it `Determines` (related to [DeepConsAnalysisRes](09_deepconsanalysisres.md)).

3.  **`searchOrder left`**: This finds the optimal generation order. It leverages functions like `assignPriorities` and `propagatePri` to determine dependencies and prioritize arguments. The `left` argument is a `FinMap` of `Determination` (which includes `stronglyDeterminingArgs` and `argsDependsOn`) for the constructor's arguments.

    ```idris
    -- A simplified view of part of `LeastEffort.consGenExpr`
    -- src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr

    -- ...
    -- Compute determination map without weak determination information
    let determ = insertFrom' empty $ mapI (\i, ta => (i, ta.determ)) argsTypeApps
    -- ...
    -- Compute the order for internal generation
    let theOrder = userImposed ++ searchOrder (removeDeeply userImposed nonDetermGivs)
    -- ...
    ```
    `theOrder` is a `List (Fin con.args.length)` (a list of indices of the constructor's arguments) that represents the sequence in which `DepTyCheck` should generate the arguments.

4.  **`genForOrder order` Block:** This is where the core `do` block is built. It iterates through `theOrder`.

    ```idris
    -- A simplified view of part of `LeastEffort.consGenExpr`
    -- src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr

    let genForOrder : List (Fin con.args.length) -> m TTImp
        -- `state` tracks arguments that are already present (given or generated)
        genForOrder order = map (foldr apply callCons) $ evalStateT givs $ for order $ \genedArg => do
            -- ...
            -- Form an expression to call the subgen
            (subgenCall, reordering) <- callGen subsig subfuel $ snd <$> subgivens -- This calls DerivationClosure!
            -- ...
            -- Form an expression of binding the result of subgen
            let genedArg:::subgeneratedArgs = genedArg:::subgeneratedArgs <&> bindVar . flip Vect.index bindNames
            -- ...
            let bindSubgenResult = foldr (\l, r => var `{Builtin.DPair.MkDPair} .$ l .$ r) genedArg subgeneratedArgs
            -- ...
            -- Chain the subgen call with a given continuation
            pure $ \cont => `(~subgenCall >>= ~(bindRHS cont))
    ```
    *   `callCons`: This function creates the final `pure MkPost id' author' title'` part of the `do` block.
    *   The `for order $ \genedArg => do ...` loop processes each argument in `theOrder`.
    *   `callGen subsig subfuel ...`: This is where `consGenExpr` delegates to [DerivationClosure](06_derivationclosure.md)'s `callGen` to get the actual `TTImp` for generating the argument (e.g., `genNat fuel`).
    *   `pure $ \cont => `(~subgenCall >>= ~(bindRHS cont))``: This builds up the `TTImp` for the `do` block, chaining generated arguments with `>>=`. `bindRHS` handles binding the generated value to a variable like `id'`.

5.  **`labelGen "\{show con.name} (orders)".label <$> genForOrder theOrder`**: Finally, after the entire `do` block's `TTImp` is generated, it is wrapped with a [CTLabel](04_ctlabel__compile_time_label__.md).

**Other Tactics:** Notice that the `DeriveBodyRhsForCon.Impl.idr` file also outlines comments for other potential tactics like `BestEffort`, `FailFast`, and `DecEqConflicts`. These are currently placeholders (`?cons_body_..._rhs`) but illustrate that `DepTyCheck` is designed to support different generation strategies depending on the complexity of external generators and dependency resolution.

## Conclusion

`DeriveBodyRhsForCon` is the sophisticated piece of `DepTyCheck` that synthesizes all the analysis and helper functions into runnable code.

You've learned:
*   `DeriveBodyRhsForCon` is an interface that defines how the right-hand side of a constructor's generator should be derived.
*   Its `consGenExpr` method takes a `GenSignature`, a `Con`, `given` arguments, and `fuel` to produce the necessary `TTImp` (Idris code).
*   The `LeastEffort` tactic is the default implementation, which orchestrates the generation order, calls sub-generators via [DerivationClosure](06_derivationclosure.md), chains them into a `do` block, and applies [CTLabel](04_ctlabel__compile_time_label__.md)s for debugging.
*   This mechanism transforms high-level type definitions into concrete, working generators that embody all the properties (`Emptiness`, `Fuel` management, `ModelCoverage`) discussed in previous chapters.

This concludes our journey through the fundamental concepts of `DepTyCheck`! You now have a foundational understanding of how this powerful library automatically generates test data for your Idris programs, especially for those complex dependent types.

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)