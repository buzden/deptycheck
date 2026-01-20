# Chapter 11: Primitive Imperative Language (PIL) Examples

## Introduction

The Primitive Imperative Language (PIL) examples represent the most advanced application of DepTyCheck, demonstrating its capability to generate entire, valid computer programs. These examples showcase how to define programming language semantics using Idris's dependent types and automatically generate type-safe programs.

### Learning Objectives
- Understand how to define programming language semantics with dependent types
- Learn techniques for automatic program generation
- Explore multi-language compilation and testing
- Master state tracking and transformation in program generation

### The Ultimate Challenge: Generating Correct Programs
Imagine building a compiler for a new programming language. You need thousands of test programs, but manual creation is impractical. PIL examples solve this by:
- Defining language rules using dependent types
- Using DepTyCheck to automatically generate valid programs
- Ensuring programs are both syntactically and semantically correct

## PIL Overview

### What is PIL?
PIL is a family of small programming languages embedded in Idris that use dependent types to enforce language semantics at compile time. The type system acts as a built-in compiler, preventing common programming errors.

### Key Concepts
- **State Tracking**: PIL programs track variable and register state through type-level annotations
- **Type Safety**: Programs are guaranteed to be syntactically and semantically correct
- **Automatic Generation**: DepTyCheck can generate complex programs automatically
- **Multi-Language Support**: Programs can be compiled to multiple target languages

## PIL-Reg: Imperative Language with Registers

### Language Definition
PIL-Reg models an assembly-like language with named variables and CPU registers. The `Statement` type tracks program state transformations:

```idris
data Statement : (preV : Variables) -> (preR : Registers rc) ->
                 (postV : Variables) -> (postR : Registers rc) -> Type
```

This type signature represents a transformation from a "before" state (`preV`, `preR`) to an "after" state (`postV`, `postR`), where:
- `preV`/`postV`: Lists of variables available before/after the statement
- `preR`/`postR`: State of CPU registers before/after the statement

A `Registers rc` value is a list of length `rc` where each element indicates `Maybe` the `Type'` of data stored in that register. For example, `[Just Int', Nothing, Just String']` means register 0 holds an `Int`, register 1 is empty, and register 2 holds a `String`.

### Core Constructors

#### Variable Declaration
```idris
(.) : (ty : Type') -> (n : Name) -> Statement vars regs ((n, ty)::vars) regs
```

#### Register Assignment
```idris
(%=) : (reg : Fin rc) -> Expression vars preR ty ->
       Statement vars preR vars (preR `With` (reg, Just ty))
```

This statement takes a "before" register state `preR` and produces an "after" state `preR `With` (reg, Just ty)`. The `With` operation is a type-level instruction that updates the register state to show that register `reg` now definitely contains a value of type `ty`.

#### Register Reading
```idris
R : (r : Fin rc) -> (0 _ : IsJust $ index r regs) => Expression ...
```

To read from a register `r`, you must provide a proof that the register is initialized (`IsJust (index r regs)`). The Idris compiler prevents reading from uninitialized registers at compile time, eliminating a common runtime error.

#### Sequencing
```idris
(>>) : Statement preV preR midV midR ->
       Statement midV midR postV postR ->
       Statement preV preR postV postR
```

#### Conditionals with State Merging
```idris
If__ : (cond : Expression ...) ->
       (thenBranch : Statement ... regsThen) ->
       (elseBranch : Statement ... regsElse) ->
       Statement ... (Merge regsThen regsElse)
```

The `Merge` operation handles register state after conditional branches:
- If a register holds the same type in both branches, it retains that type
- If types differ (`Just Int'` vs `Just String'`) or one branch doesn't touch the register (`Just Int'` vs `Nothing`), the final state becomes `Nothing` (uninitialized)
- This conservative approach models the static analysis a real compiler performs

Example scenario:
```idris
if (someCondition) then
  1 %= C 100  -- Register 1 holds Int
else
  1 %= C "hello" -- Register 1 holds String
-- After merge: Register 1 becomes Nothing (uninitialized)
```

### Generation Strategy
The generator recursively builds programs by:
1. Generating individual statements
2. Tracking state transformations
3. Combining statements with proper state flow

### Generator Implementation
The `pil-reg` example uses a hand-written generator that follows the same principles as `deriveGen` but provides more control:

```idris
-- From: examples/pil-reg/src/Example/Pil/Gens.idr
statement_gen (More f) preV preR = frequency
  [ (1,   nop_gen   f preV preR) -- do nothing
  , (5,   dot_gen   f preV preR) -- declare a variable
  , (50,  v_ass_gen f preV preR) -- assign to variable
  , (50,  r_ass_gen f preV preR) -- assign to register
  , (200, seq_gen   f preV preR) -- chain two statements
  , ...
  ]
```

The `frequency` function allows weighting different statement types to guide generation toward more interesting programs.

### Automatic Generation with deriveGen
For simpler cases, `deriveGen` can automatically create generators:

```idris
-- Simplified generator using deriveGen
genStatement : Fuel -> Gen MaybeEmpty (Statement vars regs postV postR)
genStatement = deriveGen
```

When `deriveGen` analyzes the `Statement` type, it:
- Learns all constructor rules (`(%=)`, `R`, `If__`, `Merge`, `With`)
- Plans how to satisfy type-level constraints
- Generates code that only picks initialized registers for `R`
- Correctly calculates `Merge`d states for conditionals
- Automatically handles all complex program generation logic

### Example Program Generation
```idris
-- Generate a program starting from empty registers
programGen : Gen0 (postV ** postR ** Statement [] (AllUndefined {rc}) postV postR)
```

## PIL-Fun: Functional Language with Backends

### Language Features
PIL-Fun extends PIL with functional programming constructs:
- Function definitions and calls
- Lexical scoping
- Return values
- Multiple target language compilation

### Abstract Language Definition
Unlike imperative PIL-Reg, PIL-Fun uses immutable `let` bindings and represents programs as abstract syntax trees:

```idris
data Stmts : (funs : Funs) -> (vars : Vars) ... -> Type where
  -- `let x = initial in cont`
  NewV : (initial : Expr ... ty) ->
         (cont : Stmts funs (vars :< ty) ...) ->
         Stmts funs vars ...

  -- `if (cond) { th } else { el }; cont`
  If   : (cond : Expr ... Bool') ->
         (th, el : Stmts ...) ->
         (cont : Stmts ...) ->
         Stmts ...

  -- `return x`
  Ret  : Expr ... retTy -> Stmts ... (Just retTy)

  -- The end of a block that returns nothing
  Nop  : Stmts ... Nothing
```

### Function Signatures
```idris
record FunSig where
  constructor (==>)
  From : SnocListTy  -- Argument types
  To   : MaybeTy     -- Return type
```

A signature like `[< Int', Int'] ==> Just Int'` represents a function that takes two `Int`s and returns an `Int`. A signature like `[< Int'] ==> Nothing` represents a function that takes one `Int` and returns nothing (like a `print` function).

### Function Definition
```idris
NewF : (sig : FunSig) ->
       (body : Stmts funs (vars ++ sig.From) sig.To) ->
       (cont : Stmts (funs :< sig) vars retTy) ->
       Stmts funs vars retTy
```

This constructor demonstrates sophisticated type-level engineering:
1. `sig`: The function signature
2. `body`: The function's code, operating in a new scope `vars ++ sig.From` (current variables plus function arguments)
3. `cont`: The continuation code that knows about the newly defined function `funs :< sig`

### Multi-Language Support
PIL-Fun includes pretty-printers for:
- Scala 3
- Lua 5.4
- Idris 2

### Transpiling to Other Languages
The most powerful feature of PIL-Fun is its ability to transpile generated programs to multiple target languages:

**Generated PIL Program**:
- Define function `f0` that takes `Int` argument `v0` and returns `v0 > 10`
- Declare variable `v1`
- Call `f0` with argument `20`
- Assign result to `v1`

**Scala 3 Output**:
```scala
def f0(v0 : Int): Boolean =
  v0 > 10

val v1 : Boolean =
  f0(20)
```

**Lua 5.4 Output**:
```lua
function f0(v0)
  return v0 > 10
end

local v1 = f0(20)
```

This enables differential testing across multiple language implementations.

### Pretty-Printer Implementation
Each language has a specific printer that pattern-matches on the `Stmts` structure:

```idris
printStmts (NewV initial cont) = do
  -- Generate variable name, translate expression
  rhs <- printExpr initial
  -- Translate to "val nm = <rhs>" in Scala
  pure $ ("val" <++> nm <++> "=" <++> rhs) `vappend` !(printStmts cont)
```

The printers recursively walk the AST, translating each constructor to target language syntax.

### Execution Pipeline
When running `pil-fun scala3`, the system performs:
1. Generate abstract program using `genStmts`
2. Select appropriate pretty-printer (`printScala3`)
3. Translate AST to target language
4. Output formatted code

### Pipeline Implementation
The core logic elegantly chains generation and translation:

```idris
run : Config -> ... -> (pp : PP language) -> IO ()
run conf ... pp = do
  seed <- conf.usedSeed
  -- Generate program, then pretty-print it
  let vals = unGenTryN conf.testsCnt seed $
               genStmts ... >>= pp ...
  -- Print each result
  Lazy.for_ vals $ \val => putStrLn val
```

This creates a lazy list of generated and translated programs, demonstrating how the generator monad can chain complex operations.

### Abstract Syntax Tree Generation
The generator creates `Stmts` values representing abstract programs, which are then translated to concrete syntax.

### Automatic Generation with deriveGen
```idris
-- From: examples/pil-fun/src/Language/PilFun/Derived.idr
genStmts : Fuel -> (funs : Funs) -> (vars : Vars) -> (retTy : MaybeTy) ->
           Gen MaybeEmpty (Stmts funs vars retTy)
genStmts = deriveGen
```

This one-line definition creates a generator that can build arbitrarily complex programs with functions, loops, and variables, all while guaranteeing type safety.

### Pretty-Printer Interface
```idris
PP : SupportedLanguage -> Type
PP language = {funs : _} -> {vars : _} -> {retTy : _} ->
              (names : UniqNames language funs vars) =>
              Fuel -> Stmts funs vars retTy -> Gen0 $ Doc opts
```

### How deriveGen Handles Function Generation
When generating a `NewF` constructor, `deriveGen` follows this sophisticated process:

1. **Choose Constructor**: Randomly selects `NewF` for generating a function
2. **Generate Signature**: Creates a random `FunSig` (e.g., `[< Int'] ==> Just Bool'`)
3. **Generate Body**: Makes recursive call with new context: `genStmts fuel funs (vars ++ [< Int']) (Just Bool')`
4. **Generate Continuation**: Makes recursive call with updated function list: `genStmts fuel (funs :< sig) vars retTy`

This approach navigates complex dependencies by generating each part in the correct context, demonstrating `deriveGen`'s ability to handle mutual recursion and scope management.

## PIL-Dyn: Dynamic Register Management

### Flexible State Handling
PIL-Dyn demonstrates DepTyCheck's adaptability with different generation constraints:
- **Open-ended**: Generate any valid program
- **Goal-oriented**: Generate programs meeting specific state requirements
- **Constraint-based**: Generate programs transforming specific states

### Core Instructions

#### Assign Instruction
```idris
Assign : (target : Fin r) ->
         (expr : Expr ins t) ->
         (cont : LinBlock (update target (Just t) ins) outs) ->
         LinBlock ins outs
```

When assigning to a register, the continuation operates in the updated state where the target register holds the expression's type.

#### End Instruction
```idris
End : ReducesTo ins outs => LinBlock ins outs
```

Requires a proof that the current state `ins` is compatible with the promised output state `outs`, ensuring the program fulfills its contract.

### The LinBlock Type
```idris
data LinBlock : (ins, outs : Regs r) -> Type
```

This signature represents a "linear block" of instructions that transforms register state `ins` into register state `outs`. A `Regs r` value is a list representing the state of `r` registers, where each element indicates `Maybe` the type of data stored.

### Generation Scenarios

#### Scenario 1: Total Freedom
```idris
genLinBlock'' : Fuel -> ... => Gen MaybeEmpty (ins ** outs ** LinBlock ins outs)
```

**What we're asking**: "Generate any valid program and tell me what its input/output states are."
**Result example**: `([Nothing,Nothing] ** [Just I,Just B] ** myProgram)` - program starting with empty registers ending with Int and Bool

#### Scenario 2: Known Destination
```idris
genLinBlock'_ : Fuel -> ... => (outs : Regs r) -> Gen MaybeEmpty (ins ** LinBlock ins outs)
```

**What we're asking**: "Generate a program that ends with specific register state `outs`."
**Result example**: Given `[Just I, Nothing]`, generates program starting from `[Just I, Just B]` that clears register 1

#### Scenario 3: Known Starting Point
```idris
genLinBlock_' : Fuel -> ... => (ins : Regs r) -> Gen MaybeEmpty (outs ** LinBlock ins outs)
```

**What we're asking**: "Generate a program starting from specific state `ins` and tell me the final state."
**Result example**: Given `[Just I, Nothing]`, generates program ending with `[Just I, Just B]`

#### Scenario 4: Full Contract
```idris
genLinBlock__ : Fuel -> ... => (ins, outs : Regs r) -> Gen MaybeEmpty (LinBlock ins outs)
```

**What we're asking**: "Find a program that transforms `ins` exactly to `outs`."
**Result example**: `[Nothing, Nothing]` → `[Just I, Just B]` succeeds, but `[Just I]` → `[Just B]` fails (no Int→Bool conversion)

## Implementation Patterns

### Common Generation Patterns
- **Recursive State Propagation**: Using output state as input for next generation
- **Type-Guided Construction**: Leveraging dependent types for correctness
- **Modular Architecture**: Separating generation from language semantics

### Generator Signatures
Different PIL variants demonstrate various generator patterns:
- State-transforming generators
- Context-aware generation
- Multi-stage generation pipelines

### Recursive Generation Example
```idris
seq_gen : Fuel -> ... -> Gen0 (postV ** postR ** Statement preV preR postV postR)
seq_gen f preV preR = do
  (midV ** midR ** left) <- statement_gen f preV preR
  (postV ** postR ** right) <- statement_gen f midV midR
  pure (postV ** postR ** left >> right)
```

This elegant `do` block captures the core logic:
1. Generate the first statement `left` and capture its resulting state `(midV, midR)`
2. Use that intermediate state to generate the second statement `right`
3. Combine them with `>>` to form a single, larger program

### Step-by-Step Program Generation
Let's trace how the generator builds a program:

1. **Initial State**: `vars = []`, `regs = [Nothing, Nothing]`
2. **First Statement**: Generator picks `dot_gen`, generates `Int'` and `"x"`
   - Statement: `Int'. "x"`
   - New State: `vars = [("x", Int')]`, `regs = [Nothing, Nothing]`
3. **Second Statement**: Generator picks `v_ass_gen`, assigns `C 10` to `"x"`
   - Statement: `"x" #= C 10`
   - State unchanged: `vars = [("x", Int')]`, `regs = [Nothing, Nothing]`
4. **Third Statement**: Generator picks `r_ass_gen`, assigns `V "x"` to register `0`
   - Statement: `0 %= V "x"`
   - New State: `vars = [("x", Int')]`, `regs = [Just Int', Nothing]`
5. **Final Program**: `Int'. "x" >> "x" #= C 10 >> 0 %= V "x"`

The generator tracks type-level state at every step to ensure program validity.

## Practical Applications

### Compiler Testing
PIL generation enables comprehensive compiler testing through:
- Differential testing across multiple backends
- Edge case discovery
- Regression testing

### Language Implementation Testing
- Syntax validation
- Semantic correctness verification
- Performance testing

### Compiler Fuzzing
By using DepTyCheck with PIL, you can create a **fuzz tester** for your compiler or interpreter:
- Generate millions of unique, complex programs
- Test every nook and cranny of language implementation
- Be confident you're testing semantic correctness, not just syntax

### Example Testing Workflow
1. Generate PIL program using DepTyCheck
2. Compile to multiple target languages
3. Verify semantic equivalence
4. Test edge cases and corner conditions

## Advanced Topics

### State Merging in Conditionals
How PIL handles register state merging after conditional branches:
- Conservative merging rules
- Type safety preservation
- Practical implications for program generation

### Function Scope Management
Techniques for managing:
- Variable scoping
- Function signatures
- Return type tracking

### Performance Considerations
- Generator efficiency for complex programs
- Memory usage during generation
- Optimization strategies

## Hands-On Examples

### Setting Up PIL Generation
```idris
-- Basic PIL-Reg generator setup
genStatement : Fuel -> Gen MaybeEmpty (Statement vars regs postV postR)
genStatement = deriveGen
```

### Multi-Language Compilation Example
```idris
-- Generate and compile to multiple languages
runMultiLanguageTest : IO ()
runMultiLanguageTest = do
  program <- generatePILProgram
  scalaCode <- printScala3 program
  luaCode <- printLua5_4 program
  -- Test compilation and execution
```

### Custom Language Extension
```idris
-- Extending PIL with new language features
data ExtendedStatement : ... -> Type where
  -- Add new language constructs
  Loop : Expression ... -> Statement ... -> ExtendedStatement ...
  -- Implement generation rules
```

## Best Practices

### Language Design Guidelines
- Keep type signatures clear and manageable
- Use dependent types judiciously
- Maintain separation between language definition and generation

### Generator Implementation Tips
- Start with simple language features
- Test generation incrementally
- Use meaningful weights in frequency distributions

### Testing Strategies
- Test with small programs first
- Verify generated program correctness
- Use multiple generation strategies

## Conclusion

The PIL examples demonstrate DepTyCheck's full potential for program generation. By combining dependent types with automatic generation, developers can create robust testing frameworks for programming languages and compilers.

### Key Takeaways
- Dependent types enable precise language semantics
- Automatic generation scales testing capabilities
- Multi-language support enhances practical utility
- State tracking ensures program correctness

### Future Directions
- Extending PIL with more language features
- Adding additional target languages
- Performance optimization techniques
- Integration with existing compiler frameworks

## Further Reading

### Related Chapters
- Chapter 1: Generator Monad (Gen)
- Chapter 2: Automatic Generator Derivation (deriveGen)
- Chapter 3: Coverage Analysis
- Chapter 4: Recursion Analysis

### External Resources
- Idris documentation on dependent types
- Property-based testing methodologies
- Compiler construction techniques