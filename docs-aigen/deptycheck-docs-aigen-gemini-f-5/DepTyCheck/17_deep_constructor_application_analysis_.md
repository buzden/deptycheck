# Chapter 17: Deep Constructor Application Analysis

Welcome back! In [Chapter 16: Constructor Body Derivation](16_constructor_body_derivation_.md), we began to break down how `DepTyCheck` builds the specific code for a generator that targets a single constructor. We briefly mentioned that a crucial, complex step in that process involves understanding how constructor arguments influence the type itself, especially in GADT patterns. Now, we're dedicating an entire chapter to this intricate process: **Deep Constructor Application Analysis**.

## What Problem Does Deep Constructor Application Analysis Solve?

Imagine you have a special kind of "smart paint mixer." You tell it, "I need a light blue paint." The mixer then identifies its core ingredients (blue pigment, white pigment) and applies them. But what if you say, "I need a paint that perfectly matches the `Fin (S k)` value I have here, which is '0' (meaning `FSucc FZ`)"?

This is where things get tricky. The mixer needs to look *deep inside* the `Fin (S k)` value. It needs to see that `(S k)` is actually derived from the `k` inside `FSucc FZ`. It needs to connect these internal pieces to figure out the right mix.

In Idris, especially with Generalised Algebraic Data Types (GADTs), a constructor argument might not just be a simple value. It can be an *expression* that deeply applies other constructors and free variables, ultimately determining the *index* of the GADT.

Consider a GADT like this:

```idris
data MyGADT : Nat -> Type where
  MkOne :                               MyGADT 1
  MkTwo :                               MyGADT 2
  MkPair : (x : MyGADT n) -> (y : MyGADT m) -> MyGADT (n + m)
```

If `DepTyCheck` is deriving a generator for `MyGADT (n + m)`, and it wants to use `MkPair`, it needs to know:
*   How does `(n + m)` relate to the arguments `x` and `y`?
*   Specifically, how does `n` come from `x` and `m` from `y`?

The problem Deep Constructor Application Analysis solves is: **how can `DepTyCheck` examine a complex expression (likely a GADT index) and figure out which free variables (unbound names) contribute to it, how they are combined using data constructors, and whether these free variables determine the overall type?** This is crucial for matching GADT patterns and generating correct `decEq` checks. It's like having a special scanner that deconstructs complex Lego structures to see which individual bricks (free variables) were used and how they fit together, even if hidden inside other parts.

Our central use case for this chapter is: **To analyze a GADT index expression (e.g., `(n + m)` in `MyGADT (n + m)`) and determine which free variables (`n`, `m`) are used within it, effectively tracing how constructor arguments influence the type index.**

## The Core Idea: Deconstructing Expressions and Finding Free Variables

This analysis works by recursively deconstructing an expression. It starts at the top of an expression (like `n + m`) and works its way down. If it sees a constructor application (like `(+)`), it drills into its arguments. If it sees a free variable, it records it.

### `analyseDeepConsApp`: The Deep Scanner

The function that performs this deep analysis is `analyseDeepConsApp`. It tries to treat an expression as a "deeply nested application of data constructors to free variables."

```idris
-- From src/Deriving/DepTyCheck/Util/DeepConsApp.idr (simplified signature)

export
analyseDeepConsApp : NamesInfoInTypes =>
                     MonadError String m =>
                     MonadWriter (List Name) m =>
                     (collectConsDetermInfo : Bool) ->
                     (freeNames : SortedSet Name) ->
                     (analysedExpr : TTImp) ->
                     m $ DeepConsAnalysisRes collectConsDetermInfo
```

**Explanation of the `analyseDeepConsApp` signature:**

*   `NamesInfoInTypes`: Provides information about names (e.g., if a name is a known constructor).
*   `MonadError String m`, `MonadWriter (List Name) m`: These are capabilities. The function can `throwError` if it finds something it doesn't understand, and it can `tell` (write) a list of `Name`s (the free variables it finds) as it goes along.
*   `collectConsDetermInfo : Bool`: A flag. If `True`, it collects additional information (about whether the constructor determines the type).
*   `freeNames : SortedSet Name`: This is a list of *known free variables* that `DepTyCheck` expects to find within the expression. This is important for identifying variables vs. other things.
*   `analysedExpr : TTImp`: This is the `TTImp` (the Idris internal representation) of the complex expression we want to analyze (our GADT index `(n + m)`).
*   `m $ DeepConsAnalysisRes collectConsDetermInfo`: The result is either a list of `Name`s (the discovered free variables) or a more complex structure (`appliedFreeNames ** BindExprFun`) if `collectConsDetermInfo` is `True`. `BindExprFun` is a helper for creating a new expression where the free variables are replaced by *bound variables*.

## How `analyseDeepConsApp` Works (Simplified Internal Flow)

Let's trace how `analyseDeepConsApp` would look at `(n + m)` from our `MkPair` constructor, given that `n` and `m` are in `freeNames`.

```idris
-- Simplified internal logic within analyseDeepConsApp

isD : TTImp -> m $ DeepConsAnalysisRes ccdi
isD e = do
  -- 1. Try to deconstruct the expression `e`
  let (headExpr, args) = unAppAny e -- `unAppAny` splits an expression into its head and arguments

  -- 2. Check if `headExpr` is a variable (`IVar`)
  case headExpr of
    IVar _ lhsName =>
      -- Is `lhsName` one of our `freeNames`?
      if contains lhsName freeNames
        then
          -- Yes, it's a free variable! Record it.
          tell [lhsName]
          if null args
            then pure [lhsName] -- Simple free variable (like `n` or `m`)
            else throwError "applying free name to some arguments" -- Cannot apply args to a simple free variable
        else
          -- If not a free name, is it a constructor? (like `(+)`)
          let Just con = lookupCon lhsName -- Check if `lhsName` is a known constructor
            | Nothing => throwError "name is not a constructor or free variable"
          -- If it is a constructor:
          -- Recursively call `isD` on each `arg` in `args`.
          deepArgsResults <- for args $ \anArgExp => isD anArgExp
          -- Merge all the free names found in the `deepArgsResults`.
          pure $ flatten deepArgsResults -- Collect all free names from sub-expressions.

    -- 3. If `headExpr` is not a variable, or other cases:
    --    Handle primitive values (`IPrimVal`), types (`IType`), etc.
    --    Often means it's not a `DeepConsApp` or an error.
    _ => throwError "not an application to a variable"
```

**Step-by-step conceptual walkthrough for `analyseDeepConsApp` on `(n + m)`:**

1.  **Input:** `analysedExpr = ` (`(+) n m`) (internal `TTImp` for `n + m`). `freeNames = {n, m}`.
2.  **`isD ` ((+) n m)`:**
    *   `unAppAny ` ((+) n m) ` ` returns `headExpr = (+)` and `args = [n, m]`.
    *   `lhsName = (+)`: Not in `freeNames`.
    *   `lookupCon (+)`: Yes, `(+)` is a constructor (it's really a function that is like a constructor for `Nat`).
    *   **Recursive calls:**
        *   `isD n`:
            *   `headExpr = n`, `args = []`.
            *   `lhsName = n`: **In `freeNames`!**
            *   `tell [n]`.
            *   `pure [n]`.
        *   `isD m`:
            *   `headExpr = m`, `args = []`.
            *   `lhsName = m`: **In `freeNames`!**
            *   `tell [m]`.
            *   `pure [m]`.
    *   `deepArgsResults` will contain `[[n], [m]]`.
    *   `flatten deepArgsResults` results in `[n, m]`.
    *   **Returns:** `[n, m]` (the list of free variables found).

The `analyseDeepConsApp` successfully identified that `n` and `m` are the free variables used in the expression `(n + m)`.

### Beyond Free Names: `BindExprFun` and `ConsDetermInfo`

The actual `analyseDeepConsApp` is more powerful. It can also:

*   **Construct a `BindExprFun`:** This is a function that takes a list of *new* names (bound variables) and constructs a new `TTImp` where the original free variables (like `n` and `m`) are replaced by these new bound variables. This is crucial for `DepTyCheck` to build new code templates correctly.
*   **Generate `ConsDetermInfo`:** This helps track if an expression (or part of it) *determines* the overall type (i.e., if it's responsible for fixing a GADT index).

    ```idris
    -- From src/Deriving/DepTyCheck/Util/DeepConsApp.idr

    public export
    data ConsDetermInfo = DeterminedByType | NotDeterminedByType
    ```
    This `ConsDetermInfo` helps decide if we need `decEq` checks for this part of the expression. If a constructor *determines* part of the type, we might need to check if that determined part matches the original GADT index value.

## Central Use Case in Action: `canonicConsBody` and `analyseDeepConsApp`

Let's revisit how this is used in [Chapter 16: Constructor Body Derivation](16_constructor_body_derivation_.md)'s `canonicConsBody`.

Recall the `deepConsApps` variable:

```idris
-- From src/Deriving/DepTyCheck/Gen/ForOneTypeCon/Impl.idr (simplified from previous chapter)

    let deepConsApps : Vect _ $ Either (String, TTImp, List Name) _ := sig.givenParams.asVect <&> \idx => do
      -- `sig.givenParams` refers to the original GADT indices we are trying to match.
      -- `conRetTypeArg idx` is the expression for that index *as it appears in the constructor's return type*.
      -- Example: for `MkPair (x : MyGADT n) (y : MyGADT m) : MyGADT (n + m)`,
      -- if `idx` points to the `Nat` index of `MyGADT`, then `conRetTypeArg idx` would be `(n + m)`.

      let argExpr = conRetTypeArg idx
      let (ei, fns) = runWriter $ runEitherT {e=String} {m=Writer _} $ analyseDeepConsApp True conArgNames argExpr
      -- `analyseDeepConsApp True conArgNames argExpr` here:
      --   `True` means collect `ConsDetermInfo`
      --   `conArgNames` are the constructor's own argument names (`x` and `y` for `MkPair`)
      --   `argExpr` is the expression for the GADT index (`n + m` for `MkPair`).
      -- `fns` are the free names found (e.g., `n`, `m`).
      -- `ei` would be the results if not an error.
```

Here, `analyseDeepConsApp` takes `argExpr` (`n + m`) and `conArgNames` (`x`, `y`). It's important to remember that `n` and `m` are *not* arguments of `MkPair`; they are free variables that were part of the *type signature* for `MkPair`. `analyseDeepConsApp` will find these names and say "Aha! These are the free variables driving this GADT index." This information is then used to generate `decEq` clauses to check if `n` and `m` can be equated to the actual `Nat` indices (`n_val` and `m_val`) that the `MkPair` constructor was invoked with.

``` mermaid
sequenceDiagram
    participant ConsBody as `canonicConsBody`
    participant DeepScanner as `analyseDeepConsApp`
    participant IdrisExpr as Idris Expression (`TTImp`)
    participant FreeVarList as List of Free Vars
    participant ConsDeterm as `ConsDetermInfo`
    participant DecEqGen as `decEq` Generator

    ConsBody->>IdrisExpr: Get GADT index expression (`argExpr` = `(n + m)`)
    ConsBody->>IdrisExpr: Get constructor argument names (`conArgNames` = `{x, y}`)
    ConsBody->>DeepScanner: `analyseDeepConsApp True conArgNames (n + m)`
    DeepScanner->>DeepScanner: Recursively analyzes `(n + m)`.
    DeepScanner->>FreeVarList: Finds `n` and `m` as free variables.
    DeepScanner->>ConsDeterm: Determines if `n` and `m` are type-determining.
    DeepScanner-->>ConsBody: Returns (`n`, `m` and their `ConsDetermInfo`) + `BindExprFun`.

    ConsBody->>DecEqGen: Uses this info to generate `decEq` checks (e.g., `decEq n n_val`, `decEq m m_val`)
    ConsBody->>Tactics: Passes `BindExprFun` to constructor RHS derivation tactics (for code generation).
```

This sequence diagram illustrates how `analyseDeepConsApp` provides the critical bridge between the symbolic GADT index expressions and the actual free variables that need to be considered when deriving the constructor's body.

## Conclusion

Deep Constructor Application Analysis, primarily handled by the `analyseDeepConsApp` function, is `DepTyCheck`'s sophisticated mechanism for understanding how deeply nested applications of data constructors to free variables contribute to a type expression, especially within GADT indices. By recursively deconstructing expressions, identifying free variables, and determining their type-determining influence, this analysis provides `DepTyCheck` with the crucial information needed to generate correct `decEq` checks and properly abstract over these variables. This meticulous detail enables `DepTyCheck` to generate accurate and type-safe generators even for highly complex, dependently typed data structures.

Next, armed with this deep understanding, we'll finally delve into the specific "tactics" `DepTyCheck` uses to derive the right-hand side of a constructor's generator in [Chapter 18: Constructor RHS Derivation Tactics](18_constructor_rhs_derivation_tactics_.md).

[Next Chapter: Constructor RHS Derivation Tactics](18_constructor_rhs_derivation_tactics_.md)

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)