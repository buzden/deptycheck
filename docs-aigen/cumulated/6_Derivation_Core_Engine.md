# Derivation Core Engine

## Introduction

In this tutorial, we will explore the DepTyCheck derivation core engine - the sophisticated pipeline architecture that automatically generates test data generators for complex dependent types. We'll build understanding through practical examples and hands-on implementation.

**What we will accomplish:** By the end of this tutorial, you will understand how DepTyCheck analyzes type dependencies, manages recursive generation, and produces efficient generator code through a multi-stage pipeline.

## Prerequisites

- Basic familiarity with Idris2 syntax
- Understanding of dependent types
- Experience with property-based testing concepts

## Core Pipeline Architecture

### The Four-Stage Assembly Line

The DepTyCheck derivation engine employs a modular pipeline architecture that breaks down the complex task of generator derivation into manageable stages. Let's examine this pipeline using a concrete example.

**Exercise: Understanding the Pipeline**

Consider this simple `Vect` type:

```idris
data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a
```

When `deriveGen` processes this type, it must:
1. Determine which constructor to use based on the input `n`
2. Handle recursion for the `::` constructor
3. Generate code for the element type `a`
4. Combine everything into valid Idris code

The pipeline accomplishes this through four specialized stages:

#### Stage 1: Type-Level Planning (`ForOneType`)

This stage takes the overall goal (e.g., "build a `Gen (Vect n a)`") and creates a derivation plan. It analyzes the type's constructors and delegates work to subsequent stages.

**Implementation Interface:**
```idris
public export
interface DeriveBodyForType where
  canonicBody : GenSignature -> Name -> m (List Clause)
```

#### Stage 2: Constructor Analysis (`ConsRecs`)

This stage examines each constructor to determine its properties:
- Is it recursive?
- How does it affect `Fuel` consumption?
- What are its dependencies?

#### Stage 3: Constructor Planning (`ForOneTypeCon`)

For each constructor, this stage plans the generation order. For `(::) : a -> Vect k a -> Vect (S k) a`, it must decide whether to generate `a` first or `Vect k a` first.

#### Stage 4: Code Assembly (`ForOneTypeConRhs`)

The final stage assembles the actual Idris code for each constructor's generator.

**Example Output:**
```idris
-- For the (::) constructor:
do val <- gen_a; tail <- gen_vect_k; pure (val :: tail)
```

**Exercise Solution:** Let's trace the pipeline for `Bool`:

```idris
data Bool = True | False
```

1. **Stage 1** analyzes `Bool` and delegates `True` and `False` to Stage 3
2. **Stage 2** determines both constructors are non-recursive
3. **Stage 3** plans simple generators for each constructor
4. **Stage 4** produces code: `pure True` and `pure False`
5. **Stage 1** combines them: `oneOf [pure False, pure True]`

### Dependency Management and Orchestration

Now let's examine how the derivation engine manages complex dependency chains. Consider this example:

```idris
data Tree a = Leaf | Node (Tree a) a (Tree a)

myGenerator : Fuel -> Gen MaybeEmpty (List (Tree String))
myGenerator = deriveGen
```

To build a generator for `List (Tree String)`, the system must first build generators for:
1. `Tree String`
2. `String` (a built-in type)

This creates a dependency chain that requires careful orchestration.

#### The Project Manager Pattern

The derivation orchestrator uses a project manager approach with two key components:

**Worklist (To-Do List):** Tracks generator blueprints that need to be designed
**Cache (Completed Blueprints):** Stores finished generator designs for reuse

#### The Derivation Loop

The orchestrator follows this algorithm:

1. **Analyze dependencies** for the target type
2. **Add dependencies** to the worklist
3. **Process worklist** recursively until all dependencies are resolved
4. **Cache results** to avoid redundant work

**Exercise: Tracing Dependency Resolution**

Trace the derivation process for `List (Tree String)`:

1. Request `List (Tree String)` → needs `Tree String`
2. Request `Tree String` → needs `String`
3. Request `String` → built-in type, cache it
4. Build `Tree String` using cached `String`
5. Build `List (Tree String)` using cached `Tree String`

**Implementation: callGen Function**

```idris
callGen : (neededSig : GenSignature) -> ... -> m TTImp
callGen neededSig fuel values = do
  -- Check cache first
  let existing = lookup neededSig !(get {stateType=SortedMap _})
  case existing of
    Just name => pure (callInternalGen name fuel values) -- Found in cache
    Nothing => do
      -- New task: add to cache and worklist
      let name = nameForGen neededSig
      modify {stateType=SortedMap _} $ insert neededSig name
      modify {stateType=List _} $ (::) (neededSig, name)
      pure (callInternalGen name fuel values)
```

**Implementation: deriveAll Loop**

```idris
deriveAll : m ()
deriveAll = do
  toDerive <- get {stateType=List _}  -- Get worklist
  put {stateType=List _} []           -- Clear worklist

  -- Process each task
  for_ toDerive (\(sig, name) => deriveOne sig name)

  -- Recursively process new dependencies
  when (not $ null toDerive) $ deriveAll
```

**Exercise Solution:** The derivation orchestrator ensures each generator is built exactly once through its cache-first approach, preventing redundant work and handling complex dependency graphs efficiently.

### State Management with Closuring Context

The derivation orchestrator maintains comprehensive state management through the `ClosuringContext`, which acts as the project manager's notebook for tracking the entire derivation process.

#### ClosuringContext Components

The context manages several critical pieces of information:

```idris
-- Conceptual structure of ClosuringContext
data ClosuringContext = MkClosuringContext
  { queue        : List (GenSignature, Name)    -- To-do list
  , derivedGens  : SortedMap GenSignature Name -- Cache of completed generators
  , writer       : (List Decl, List Decl)       -- Code collection
  }
```

**Queue (To-Do List):** Tracks generators that need to be created
**DerivedGens (Cache):** Maps type signatures to generated function names
**Writer (Code Collection):** Accumulates the final generated code

#### Mutual Recursion Handling

Consider this example with mutually recursive types:

```idris
data Even : Nat -> Type where
  Zero : Even Z
  SuccEven : Odd n -> Even (S n)

data Odd : Nat -> Type where
  SuccOdd : Even n -> Odd (S n)
```

When deriving generators for `Even` and `Odd`, the orchestrator must handle mutual recursion correctly.

**Exercise: Trace Mutual Recursion**

Trace how the orchestrator handles `Even` and `Odd`:

1. Request `Even` generator → needs `Odd` generator
2. Request `Odd` generator → needs `Even` generator
3. Detect mutual recursion → handle with fuel management

**Implementation: Task Queue Processing**

```idris
-- Simplified derivation loop
deriveAll : m ()
deriveAll = do
  toDerive <- get {stateType=List _}  -- Get current queue
  put {stateType=List _} []           -- Clear queue for this iteration

  -- Process each task
  for_ toDerive deriveOne

  -- Check for new dependencies added during processing
  newTasks <- get {stateType=List _}
  when (not $ null newTasks) $ deriveAll  -- Recursively process
```

**Exercise Solution:** The orchestrator detects mutual recursion by tracking which generators have been requested but not yet completed. When it encounters a dependency that's already in the queue, it handles it through fuel-based recursion control rather than getting stuck in an infinite loop.

### Recursive Derivation Handling

The derivation orchestrator employs sophisticated algorithms to handle recursive and mutually recursive type dependencies. Let's examine how it manages complex dependency graphs.

#### Work Loop Algorithm

The orchestrator's main processing loop follows this recursive pattern:

```idris
-- Core derivation loop
deriveAll : m ()
deriveAll = do
  -- Get snapshot of current worklist
  toDerive <- get {stateType=List _}
  put {stateType=List _} []  -- Clear worklist for this iteration

  -- Process each task
  for_ toDerive deriveOne

  -- Check if new dependencies were discovered
  newTasks <- get {stateType=List _}
  when (not $ null newTasks) $ assert_total deriveAll
```

**Exercise: Analyze Dependency Resolution**

Consider this complex type hierarchy:

```idris
data Expr = Var String | App Expr Expr | Lam String Expr
data Value = Closure String Expr Env | Primitive Int
data Env = EmptyEnv | Extend String Value Env
```

Trace how the orchestrator handles deriving `Expr`:

1. Request `Expr` → needs `String` (built-in), `Expr` (recursive), `String` again
2. Request `Value` → needs `String`, `Expr`, `Env`
3. Request `Env` → needs `String`, `Value`, `Env` (recursive)

**Implementation: Dependency Detection**

The `callGen` function detects dependencies and manages the worklist:

```idris
callGen : GenSignature -> ... -> m TTImp
callGen sig = do
  -- Check cache first
  let Nothing = SortedMap.lookup sig !get
    | Just name => pure (callExistingGen name)

  -- New dependency detected
  let name = nameForGen sig
  modify $ insert sig name           -- Add to cache
  modify {stateType=List _} $ (::) (sig, name)  -- Add to worklist

  pure (callFutureGen name)  -- Return placeholder
```

**Exercise Solution:** The orchestrator handles complex dependencies by:
1. Detecting recursion through cache lookups
2. Using fuel-based termination for recursive cases
3. Processing dependencies in topological order
4. Assembling code only when all dependencies are resolved

### Code Generation Workflow

The derivation closure management system coordinates the entire code generation process through a sophisticated state management system.

#### ClosuringContext: The Project Manager's Toolkit

The `ClosuringContext` provides comprehensive state management capabilities:

```idris
-- Conceptual structure of the multi-faceted context
ClosuringContext m =
  ( MonadReader (SortedMap GenSignature (ExternalGenSignature, Name)) m  -- External generators
  , MonadState (SortedMap GenSignature Name) m                          -- Started internal generators
  , MonadState (List (GenSignature, Name)) m                             -- To-do list queue
  , MonadState Bool m                                                    -- Loop initiation flag
  , MonadState (SortedSet Name) m                                        -- Weighting functions
  , MonadWriter (List Decl, List Decl) m                                 -- Generated code
  )
```

**Exercise: Trace Code Generation**

Trace the code generation for `List (Maybe Int)`:

1. Request `List (Maybe Int)` → added to queue
2. Process `List (Maybe Int)` → needs `Maybe Int`
3. Add `Maybe Int` to queue
4. Process `Maybe Int` → needs `Int`
5. Add `Int` to queue
6. Process `Int` → built-in type, generate code
7. Process `Maybe Int` → generate code using `Int` generator
8. Process `List (Maybe Int)` → generate code using `Maybe Int` generator

#### DerivationClosure Interface

The `DerivationClosure` interface defines the core responsibilities:

```idris
public export
interface Elaboration m => NamesInfoInTypes => ConsRecs => DerivationClosure m where
  needWeightFun : TypeInfo -> m ()
  callGen : (sig : GenSignature) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> m (TTImp, Maybe (gend ** Vect gend $ Fin gend))
```

**Implementation: callGen Function**

The `callGen` function orchestrates the entire derivation process:

```idris
callGen sig fuel values = do
  -- Check loop initiation
  startLoop <- get {stateType=Bool}
  put False

  -- Check external generators first
  let Nothing = lookupLengthChecked sig !ask
    | Just (name, Element extSig lenEq) =>
        pure (callExternalGen extSig name (var outmostFuelArg) ..., Just ...)

  -- Handle internal generators
  internalGenName <- do
    -- Check if already started
    let Nothing = SortedMap.lookup sig !get
      | Just name => pure name

    -- New generator: add to queues
    let name = nameForGen sig
    modify $ insert sig name           -- Add to started list
    modify {stateType=List _} $ (::) (sig, name)  -- Add to to-do list
    pure name

  -- Process queue if initiating
  when startLoop $ deriveAll

  pure (callCanonic sig internalGenName fuel values, Nothing)
```

#### deriveAll: The Processing Loop

The `deriveAll` function processes the entire derivation queue:

```idris
deriveAll : m ()
deriveAll = do
  toDerive <- get {stateType=List _}  -- Get current queue
  put {stateType=List _} []           -- Clear queue

  -- Process each generator
  for_ toDerive deriveOne

  -- Recursively process new dependencies
  when (not $ null toDerive) $ assert_total deriveAll
```

**Exercise Solution:** The code generation workflow ensures that:
1. All dependencies are resolved before code generation
2. Each generator is derived exactly once
3. External generators are prioritized when available
4. The entire dependency closure is managed efficiently
5. Generated code is collected systematically

## Implementation Walkthrough

### Setting Up the Derivation Context

The derivation process begins with the `runCanonic` function, which initializes the entire derivation context:

```idris
-- Entry point for the derivation engine
export
runCanonic : ... -> (forall m. DerivationClosure m => m a) -> Elab (a, List Decl)
runCanonic exts calc = do
  -- Set up external generators, empty task queue, and initial state
  -- Execute the main derivation calculation
  -- Return generated declarations
```

**Exercise: Context Initialization**

What components are initialized by `runCanonic`?

1. External generator mappings
2. Empty task queue
3. Empty cache
4. Code collection writer
5. Loop initiation flag

### Processing Type Dependencies

The derivation engine processes dependencies through a sophisticated task queue system. Let's examine the `deriveAll` function:

```idris
deriveAll : m ()
deriveAll = do
  toDerive <- get {stateType=List _}  -- Get current task queue
  put {stateType=List _} []           -- Clear queue for this iteration

  -- Process each task
  for_ toDerive deriveOne

  -- Recursively process new dependencies
  when (not $ null toDerive) $ assert_total deriveAll
```

**Implementation: deriveOne Function**

```idris
deriveOne : (GenSignature, Name) -> m ()
deriveOne (sig, name) = do
  -- Generate type signature
  genFunClaim <- export' name $ canonicSig sig

  -- Generate function body
  genFunBody <- def name <$> assert_total canonicBody sig name

  -- Collect generated code
  tell ([genFunClaim], [genFunBody])
```

### Handling Recursive Types

The engine handles recursive types through fuel-based termination and dependency detection:

**Example: List Generator**

```idris
data List a = Nil | Cons a (List a)

-- Generated code structure
genListImpl : Fuel -> (Fuel -> Gen MaybeEmpty a) => Gen MaybeEmpty (List a)
genListImpl fuel genA =
  case fuel of
    Dry => oneOf [pure Nil]  -- Only non-recursive option
    More subFuel => frequency
      [ (1, pure Nil)
      , (1, [| Cons !(genA subFuel) !(genListImpl subFuel genA) |])
      ]
```

**Exercise: Recursion Detection**

How does the engine detect mutual recursion between `Even` and `Odd` types?

```idris
data Even : Nat -> Type where
  Zero : Even Z
  SuccEven : Odd n -> Even (S n)

data Odd : Nat -> Type where
  SuccOdd : Even n -> Odd (S n)
```

### Generating Constructor Code

The final code generation is handled by the `consGenExpr` function, which uses dependency analysis to determine the correct generation order:

**Implementation: Argument Order Planning**

```idris
-- Dependency analysis for constructor arguments
searchOrder : Map Arg (Set OtherArgs) -> List Arg
searchOrder dependencies =
  -- Perform topological sort based on dependencies
  -- Respect user-provided ordering hints
  -- Ensure valid generation sequence
```

**Example: Dependent Pair Generation**

```idris
-- For (n ** Vect n Bool)
do
  n <- deriveGen fuel      -- Generate n first
  vec <- deriveGen fuel   -- Generate vector using n
  pure (n ** vec)         -- Combine results
```

**Exercise Solution:** The engine detects mutual recursion by tracking which generators have been requested but not yet completed in the task queue. When it encounters a dependency that's already in the queue, it uses fuel-based recursion control rather than getting stuck in an infinite loop.

### Example SortedBinTree

Imagine you have the blueprint for a `SortedBinTree`. The rule for a `Node x l r` is that everything in the left tree `l` must be smaller than the root `x`, and everything in the right tree `r` must be larger.

```idris
data SortedBinTree : Type where
  Empty : SortedBinTree
  Node  : (x : Nat) -> (l, r : SortedBinTree) ->
          AllLT x l => AllGT x r => SortedBinTree
```

When building a `Node`, what should `deriveGen` do first?
-   Option A: Generate the left tree `l` first. But how does it know the upper bound for the values? It doesn't have `x` yet!
-   Option B: Generate the root value `x` first. Now it has a reference point! It can generate a left tree `l` with values less than `x`, and a right tree `r` with values greater than `x`.

Clearly, Option B is the only logical choice. The order of generation matters. `deriveGen` needs a strategy to figure out these dependencies automatically.

### The Assembly Line Analogy

Think of `deriveGen` as commissioning a factory to build a product (your generator). The factory has an assembly line with different stations, each with a specific job.

*   **`ForAllNeededTypes` (The Factory Manager):** The manager gets the main order (e.g., "Build a `SortedBinTree` generator"). It keeps a master list of all the parts and sub-assemblies required, like a `Nat` generator and a `SortedBinTree` generator. It ensures no work is duplicated.
*   **`ForOneType` (The Product Assembly Station):** A station dedicated to assembling one specific product, like `SortedBinTree`. It knows a `SortedBinTree` can be either `Empty` or a `Node`. It's responsible for deciding which version to build.
*   **`ForOneTypeCon` (The Component Sub-Station):** A sub-station that knows how to build just one component, like a `Node`. It needs to gather all the required parts (`x`, `l`, and `r`).
*   **`ForOneTypeConRhs` (`LeastEffort`) (The Master Blueprint):** This is the instruction manual for the component sub-station. It defines the *strategy* for assembling the component. The default strategy, `LeastEffort`, tells the `Node` sub-station the correct order to gather its parts: "Get `x` first, then `l`, then `r`."

## Advanced Topics

### Performance Optimization

The derivation engine employs several optimization strategies:

1. **Caching**: Each generator is derived exactly once
2. **Lazy Evaluation**: Generators are only built when needed
3. **Topological Sorting**: Dependencies are processed in optimal order
4. **Fuel Management**: Recursion is controlled to prevent infinite loops

### Error Handling and Diagnostics

The system includes comprehensive error handling:

- **Type Safety**: Ensures generated code is well-typed
- **Dependency Validation**: Checks for circular dependencies
- **Resource Management**: Controls recursion depth with fuel
- **Debug Information**: Provides detailed error messages

### Custom Derivation Strategies

Advanced users can extend the derivation system:

```idris
-- Custom derivation interface
interface CustomDerivation m where
  customDerive : GenSignature -> m (List Clause)
```

## Implementation Details

### Four-Stage Pipeline Architecture

The derivation engine employs a sophisticated four-stage pipeline:

#### Stage 1: ForAllNeededTypes (Factory Manager)

Manages the entire derivation process and dependency resolution:

```idris
-- Simplified callGen implementation
callGen sig fuel values = do
  -- Check for external generators first
  -- Check cache for existing generators
  -- Add new generators to task queue
  -- Process queue recursively
```

```idris
-- From: src/Deriving/DepTyCheck/Gen/ForAllNeededTypes/Impl.idr

-- A loop that processes the "to-do" list
deriveAll : m ()
deriveAll = do
  -- Get the current list of tasks
  toDerive <- get {stateType=List _}
  put {stateType=List _} [] -- Clear the list

  -- For each task, create the generator
  for_ toDerive deriveOne

  -- If new tasks were added during that process, loop again!
  when (not $ null toDerive) $ assert_total $ deriveAll
```

**Job:** The Master Planner's job is to manage a "to-do" list of all the generators we need to build.

This component, found in `src/Deriving/DepTyCheck/Gen/ForAllNeededTypes/Impl.idr`, is the entry point for the whole derivation process. Its job is to manage a queue of generators that need to be built.

Its main logic can be simplified to this:
1.  Receive a request to get a generator for a `Type A`.
2.  Check its notebook: "Have I already built a generator for `Type A`?"
3.  If yes, return the existing one.
4.  If no, add "generate for `Type A`" to the to-do list, and start working on the list until it's empty.

This prevents infinite loops in recursive data types and avoids re-deriving the same generator multiple times.

#### Stage 2: ForOneType (Team Lead)

Handles derivation for a single type by delegating to constructors:

```idris
canonicBody sig n = do
  -- Get all constructors
  consBodies <- for sig.targetType.cons $ \con =>
    canonicConsBody sig (consGenName con) con
  -- Combine constructor generators
  pure (fuelDecisionExpr fuelArg consBodies)
```

```idris
-- From: src/Deriving/DepTyCheck/Gen/ForOneType/Impl.idr

-- Generates the main body for a type's generator
canonicBody sig n = do
  -- ... checks and setup ...

  -- Create a sub-generator for each constructor
  consBodies <- for sig.targetType.cons $ \con =>
    -- canonicConsBody comes from the next stage!
    canonicConsBody sig (consGenName con) con

  -- Create the main expression that chooses between constructors
  let outmostRHS = fuelDecisionExpr fuelArg ...

  pure [ ... .= local consBodies outmostRHS ]
```

The Master Planner sends a single task from its to-do list (e.g., "Make a `SortedList` generator") to this station.

**Job:** To create the overall strategy for generating *one specific type*.

This station looks at the type's definition and sees all its constructors. For `SortedList`, it sees `Nil` and `(::)`.

Its job is to write the main body of the generator function. This function will usually be a `case` expression that decides which constructor to use. For example, it might decide to use non-recursive constructors (`Nil`) if it's running out of "fuel", or choose between all constructors if it has plenty of fuel.

This station doesn't worry about the details of *how* to build a `(::)`. It just says, "Here's how you *choose* between `Nil` and `(::)`," and delegates the rest to the next station.

Its main job is to generate the top-level dispatch logic. For a recursive type, this usually means checking the `Fuel`.

It delegates the actual constructor-building logic to the `ForOneTypeCon` sub-stations.

#### Stage 3: ForOneTypeCon (Constructor Specialist)

Analyzes individual constructors and their dependencies:

```idris
canonicConsBody sig name con = do
  -- Analyze constructor arguments
  -- Determine dependencies between arguments
  -- Delegate to code assembler
```

The Recipe Strategist sends a constructor (like `SortedList`'s `(::)`) to this station.

**Job:** To analyze a single constructor and figure out its internal dependencies, especially for complex GADTs.

Remember `SortedList`'s `(::)` constructor?

```idris
(::) : (x : Nat) -> (xs : SortedList) -> IsSorted x xs => SortedList
```
It inspects this signature and finds crucial evidence:
- It sees the arguments `x` and `xs`.
- Most importantly, it sees the proof `IsSorted x xs`. It knows this proof means `x`'s value depends on `xs`'s value.
- It concludes: **You must generate `xs` *before* you can generate `x`.**

This analysis is the key to `deriveGen`'s intelligence. It prevents it from making silly mistakes like generating a random `x` and then having no way to build the rest of the list.

#### Stage 4: ForOneTypeConRhs (Component Assembler)

Generates the actual code for constructor generation:

```idris
consGenExpr sig con givs fuel = do
  -- Determine optimal generation order
  let theOrder = searchOrder dependencies
  -- Generate code for each argument
  genForOrder theOrder $ \genedArg => do
    subgenCall <- callGen typeOfGened ...
    -- Build do-block expressions
```

Finally, the plan from the Dependency Analyst ("generate `xs` first, then `x`") arrives at the last station.

**Job:** To take the generation order and write the actual, runnable `do` block code for the generator.

This is where the plan turns into reality. Knowing the order, this station writes an expression that looks like this:

```idris
-- This is the code that this stage *generates*
do
  -- Step 1: Generate the tail `xs` first
  xs <- genSortedList fuel

  -- Step 2: Now that we have `xs`, generate a valid head `x`
  -- (The generator for `x` will be constrained to <= head of `xs`)
  x <- genNatConstrained (getHead xs)

  -- Step 3: We have all the parts, now build it!
  pure (x :: xs)
```
This station's most important task is figuring out the best order to generate the arguments. It contains a function, `searchOrder`, that acts like a puzzle-solver to determine the most efficient sequence.

##### The Blueprint: `LeastEffort` Strategy

This is the real brains of the operation. The `LeastEffort` strategy is an implementation of the `DeriveBodyRhsForCon` interface. Its goal is to find the most logical order to generate a constructor's arguments.

Its logic is implemented in `searchOrder` in `src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr`. You can think of its process like this:

1.  **Analyze Dependencies:** Look at all the arguments for a constructor (like `x`, `l`, `r` for `Node`). Figure out which arguments depend on others. For `Node`, `l` and `r` depend on `x`.
2.  **Assign Priorities:** Give a low "priority score" to arguments that many others depend on. Give a high score to arguments that depend on others.
3.  **Find the Starting Point:** Find the argument with the lowest priority score that has no un-generated dependencies. This is the one to generate first. For `Node`, this is `x`.
4.  **Recurse:** Mark `x` as "generated" and repeat the process. Now `l` and `r` have their dependencies met, so they can be generated.

```idris
-- From: src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Impl.idr

-- This function implements the strategy to find the best generation order.
searchOrder : {con : _} ->
              (left : FinMap ... $ Determination con) -> -- Arguments left to generate
              List $ Fin con.args.length                  -- Returns an ordered list
searchOrder left = do
  -- 1. Find arguments with no dependencies from `left`.
  -- 2. Choose the best one based on priority.
  let Just (curr, _) = findFirstMax notDetermined
    | Nothing => []

  -- 3. Add it to our plan and remove it from the list of things to do.
  curr :: searchOrder (assert_smaller left next)
```
This simple but powerful "least effort" heuristic correctly solves the dependency puzzle for a vast range of data types, from `SortedList` to the complex `PIL` language from the last chapter.

###### Why Is This a Pluggable Strategy?

You may have noticed we said `LeastEffort` *implements* the `DeriveBodyRhsForCon` interface.

```idris
-- From: src/Deriving/DepTyCheck/Gen/ForOneTypeConRhs/Interface.idr

public export
interface DeriveBodyRhsForCon where
  consGenExpr : ... -> m TTImp
```

This interface-based design is very clever. It means that `LeastEffort` is the *default* strategy, but it's not the only one possible. If you had a special case where you needed a different assembly plan, you could (in theory) provide a different implementation of this interface.

While `DepTyCheck` only comes with `LeastEffort` out of the box, this highlights a core design principle: the derivation process is not a rigid monolith, but a flexible, customizable system. We don't have to change the entire factory—just the blueprint at one station.

## Conclusion

In this tutorial, we've explored the sophisticated derivation core engine that powers DepTyCheck's automatic generator derivation. The engine employs a multi-stage pipeline architecture with comprehensive dependency management, recursive type handling, and efficient code generation.

1.  **`ForAllNeededTypes`:** Plans all the generators that need to be built.
2.  **`ForOneType`:** Creates the top-level strategy for one type by looking at its constructors.
3.  **`ForOneTypeCon`:** Analyzes a single constructor to find dependencies.
4.  **`ForOneTypeConRhs`:** Writes the final `do` block code based on that analysis.

## Exercises

**Exercise 1: Trace Derivation**

Trace the derivation process for this complex type:

```idris
data Expr = Var String | App Expr Expr | Lam String Expr
data Value = Closure String Expr Env | Primitive Int
data Env = EmptyEnv | Extend String Value Env
```

**Exercise Solution:**
1. Request `Expr` → needs `String` (built-in), `Expr` (recursive)
2. Request `Value` → needs `String`, `Expr`, `Env`
3. Request `Env` → needs `String`, `Value`, `Env` (recursive)
4. Detect mutual recursion between `Value` and `Env`
5. Use fuel-based termination
6. Generate code with proper dependency ordering

**Exercise 2: Implement Custom Derivation**

Create a custom derivation strategy for a simple arithmetic expression type:

```idris
data ArithExpr = Num Int | Add ArithExpr ArithExpr | Mul ArithExpr ArithExpr
```

**Exercise Solution:**
```idris
instance CustomDerivation ArithExpr where
  customDerive sig = do
    -- Custom logic for arithmetic expressions
    -- Prefer smaller numbers, balanced trees
    -- Use specific weighting strategies
```

**Exercise 3: Performance Analysis**

Analyze the performance characteristics of the derivation engine for deeply nested types.

**Exercise Solution:** The derivation engine exhibits:
- Linear time complexity for non-recursive types
- Polynomial complexity for recursive types (controlled by fuel)
- Memory usage proportional to dependency graph size
- Efficient caching prevents redundant derivations