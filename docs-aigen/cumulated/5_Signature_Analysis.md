# Chapter 5: Signature Analysis

In this chapter, we'll explore how DepTyCheck understands and processes generator signatures. Signature analysis is the crucial first step that allows `deriveGen` to automatically create generators for your data types.

## Table of Contents

1. [Introduction to Signature Analysis](#introduction-to-signature-analysis)
2. [The GenSignature Record](#the-gensignature-record)
3. [Parsing Generator Signatures](#parsing-generator-signatures)
4. [External Generator Signatures](#external-generator-signatures)
5. [Practical Examples](#practical-examples)
6. [Advanced Signature Patterns](#advanced-signature-patterns)
7. [Exercises](#exercises)

## Introduction to Signature Analysis

When you use `deriveGen`, you're asking DepTyCheck to automatically create a generator function based on a type signature. But how does the system "read" your signature and understand what you want?

Signature analysis is the process of:
- Parsing generator type signatures
- Validating signature structure
- Extracting key information about what needs to be generated
- Creating a structured blueprint for code generation

Think of it as a meticulous librarian who reads your request form and translates it into a standardized work order that the rest of the system can understand.

### The Problem: Understanding Your Intent

Imagine you're ordering a custom-built computer. You might say: "I want a fast computer with 16GB RAM and an SSD." But a computer engineer needs precise specifications:
- What CPU architecture?
- What type of RAM?
- What size SSD?
- What power supply?

Similarly, when you write `deriveGen`, DepTyCheck needs to understand exactly what kind of generator you want. The type signature you provide serves as the precise specification sheet.

## The GenSignature Record

The core data structure for signature analysis is `GenSignature`. This record captures all the essential information about what a generator should produce.

```idris
-- Simplified GenSignature structure
record GenSignature where
  constructor MkGenSignature
  targetType : TypeInfo        -- The type we want to generate
  givenParams : SortedSet (Fin targetType.args.length)  -- Parameters provided by user
```

Let's break down what this means:

- **targetType**: Information about the type we're generating (e.g., `Vect`, `List`, `Maybe`)
- **givenParams**: Which of the target type's parameters are provided as inputs to the generator

### Understanding TypeInfo

The `TypeInfo` structure contains detailed information about a type:
- Type name and module
- Type parameters and their constraints
- Constructor definitions
- Argument types and names

This rich information allows DepTyCheck to understand the complete structure of the type being generated.

### Given vs Generated Parameters

A key concept in signature analysis is distinguishing between **given** and **generated** parameters:

- **Given parameters**: Provided by the user when calling the generator
- **Generated parameters**: Created by the generator itself

For example, consider this generator signature:

```idris
genVect : (len : Nat) -> Fuel -> Gen MaybeEmpty (Vect len String)
genVect = deriveGen
```

The resulting `GenSignature` would contain:
- `targetType`: Information about `Vect`
- `givenParams`: The length parameter `len` (since it's provided as input)

Now consider a different signature:

```idris
genRandomVect : Fuel -> Gen MaybeEmpty (n : Nat ** Vect n String)
genRandomVect = deriveGen
```

This signature tells DepTyCheck:
- Generate a random `Nat` called `n`
- Then generate a `Vect` of that length
- The `n` parameter is **generated**, not given

## Parsing Generator Signatures

DepTyCheck uses a function called `checkTypeIsGen` to parse and validate generator signatures. This function performs several important checks:

### The `checkTypeIsGen` Function

Located in `src/Deriving/DepTyCheck/Gen.idr`, this function is the heart of signature analysis. It performs a systematic analysis of your signature:

```idris
-- Simplified view of the parsing process
checkTypeIsGen : TTImp -> Elab GenSignature
checkTypeIsGen sig = do
  -- 1. Split signature into arguments and result
  let (sigArgs, sigResult) = unPi sig

  -- 2. Validate Fuel argument
  validateFuelArg sigArgs

  -- 3. Validate return type is Gen MaybeEmpty
  validateReturnType sigResult

  -- 4. Classify remaining arguments
  classifyArguments sigArgs

  -- 5. Extract target type information
  extractTargetType sigResult

  -- 6. Build GenSignature record
  buildGenSignature targetType givenParams
```

### 1. Fuel Argument Validation
Every generator must start with a `Fuel` parameter:

```idris
-- Valid signature
Fuel -> Gen MaybeEmpty MyType

-- Invalid signature (missing Fuel)
Gen MaybeEmpty MyType  -- Error: Fuel argument required
```

The Fuel parameter is essential for handling recursion and preventing infinite loops during generation.

### 2. Return Type Validation
The function must return a `Gen MaybeEmpty` type:

```idris
-- Valid return type
Gen MaybeEmpty (Vect n String)

-- Invalid return type
Vect n String  -- Error: Must return Gen MaybeEmpty
```

This ensures consistency across all generated functions.

### 3. Parameter Classification
Arguments are classified into different categories:

- **Given parameters**: Explicit arguments provided by the user
- **External generators**: Auto-implicit arguments (`=>`) that provide generators for sub-components
- **Implicit parameters**: Parameters with default values

```idris
-- Given parameter: (len : Nat)
-- External generator: (Fuel -> Gen MaybeEmpty a) =>
genVect : (len : Nat) -> (Fuel -> Gen MaybeEmpty a) => Fuel -> Gen MaybeEmpty (Vect len a)
```

### 4. Dependent Pair Analysis

For signatures involving dependent pairs, `checkTypeIsGen` performs additional analysis:

```idris
-- Signature with dependent pair
genSizedVect : Fuel -> Gen MaybeEmpty (n : Nat ** Vect n Bool)
genSizedVect = deriveGen
```

In this case, the function:
- Identifies `n : Nat` as a generated parameter
- Recognizes `Vect n Bool` as the target type
- Understands that `n` must be generated before `Vect` can be constructed

## External Generator Signatures

When DepTyCheck needs to use external generators (ones you've written yourself), it uses `ExternalGenSignature`:

```idris
record ExternalGenSignature where
  constructor MkExternalGenSignature
  targetType : TypeInfo
  givenParams : SortedMap (Fin targetType.args.length) (ArgExplicitness, Name)
  givensOrder : Vect givenParams.size $ Fin givenParams.size
  gendOrder   : Vect gendParamsCnt $ Fin gendParamsCnt
```

This more detailed record includes:
- **Argument explicitness**: Whether parameters are explicit or implicit
- **Argument names**: The actual names used in the signature
- **Argument ordering**: The sequence in which arguments should be passed

### When External Generators Are Used

External generators come into play in several scenarios:

1. **Auto-implicit dependencies**: When your signature includes `=>` arguments
2. **Manual generator specifications**: When you provide custom generators
3. **Library generators**: When using generators from external packages

### Example: Using External Generators

```idris
-- Custom generator for prime numbers
myPrimeGen : (max : Nat) -> Fuel -> Gen MaybeEmpty (Prime max)

-- Signature that uses the external generator
genWithPrime : Fuel -> (Fuel -> Gen MaybeEmpty (Prime max)) => Gen MaybeEmpty MyType
genWithPrime = deriveGen
```

In this case, DepTyCheck:
- Recognizes `myPrimeGen` as an external generator
- Creates an `ExternalGenSignature` with detailed calling information
- Ensures proper argument passing when invoking the external generator

### Argument Ordering Importance

The `givensOrder` and `gendOrder` fields are crucial for dependent types where argument order matters:

```idris
-- Order matters for dependent types
genComplex : (x : Nat) -> (y : Fin x) -> Fuel -> Gen MaybeEmpty ComplexType
genComplex = deriveGen
```

DepTyCheck ensures that `x` is generated before `y`, since `Fin x` depends on the value of `x`.

## Practical Examples

Let's look at some real-world signature analysis examples:

### Example 1: Simple Type Generator

```idris
genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
genTrafficLight = deriveGen
```

**Analysis:**
- Target type: `TrafficLight`
- Given parameters: None (TrafficLight has no parameters)
- External generators: None
- Generated parameters: None

**GenSignature created:**
```idris
MkGenSignature
  targetType = TrafficLight_info
  givenParams = empty_set
```

### Example 2: Dependent Type Generator

```idris
genFin : Fuel -> (n : Nat) -> Gen MaybeEmpty (Fin n)
genFin = deriveGen
```

**Analysis:**
- Target type: `Fin`
- Given parameters: `n` (the bound for Fin)
- External generators: None
- Generated parameters: None

**GenSignature created:**
```idris
MkGenSignature
  targetType = Fin_info
  givenParams = {0}  -- index of the 'n' parameter
```

### Example 3: Generator with External Dependencies

```idris
genVect : (len : Nat) -> (Fuel -> Gen MaybeEmpty a) => Fuel -> Gen MaybeEmpty (Vect len a)
genVect = deriveGen
```

**Analysis:**
- Target type: `Vect`
- Given parameters: `len`
- External generators: Generator for type `a`
- Generated parameters: None

**GenSignature created:**
```idris
MkGenSignature
  targetType = Vect_info
  givenParams = {0}  -- index of the 'len' parameter
```

### Example 4: Dependent Pair Generator

```idris
genSizedVect : Fuel -> Gen MaybeEmpty (n : Nat ** Vect n Bool)
genSizedVect = deriveGen
```

**Analysis:**
- Target type: `Vect`
- Given parameters: None
- External generators: None
- Generated parameters: `n` (created by the generator)

**GenSignature created:**
```idris
MkGenSignature
  targetType = Vect_info
  givenParams = empty_set
```

This signature tells DepTyCheck to generate both the size `n` and the vector contents.

## Advanced Signature Patterns

### Dependent Pairs
You can generate values along with their dependent parameters:

```idris
genSizedVect : Fuel -> Gen (n : Nat ** Vect n Bool)
genSizedVect = deriveGen
```

**Analysis:**
- Generated parameters: `n` (created by the generator)
- Target type: `Vect n Bool`

This pattern is particularly useful for:
- Generating values with proofs
- Creating self-contained test data
- Handling types where parameters must be generated

### Implicit Parameters
DepTyCheck handles implicit parameters correctly:

```idris
genWithImplicit : {default False flag : Bool} -> Fuel -> Gen MaybeEmpty MyType
genWithImplicit = deriveGen
```

**Analysis:**
- Implicit parameters with defaults are handled automatically
- The generator can use the default value or generate alternatives

### Multiple External Generators

You can specify multiple external generators:

```idris
genComplex : Fuel ->
            (Fuel -> Gen MaybeEmpty a) =>
            (Fuel -> Gen MaybeEmpty b) =>
            Gen MaybeEmpty (ComplexType a b)
genComplex = deriveGen
```

**Analysis:**
- Two external generators are required
- Both must be available in scope
- DepTyCheck will use them appropriately

### Nested Dependent Types

For complex nested dependencies:

```idris
genNested : Fuel -> Gen MaybeEmpty (m : Nat ** n : Nat ** Matrix m n Double)
genNested = deriveGen
```

**Analysis:**
- Generated parameters: `m` and `n`
- Target type: `Matrix m n Double`
- Parameters are generated in dependency order

### Conditional Generation

You can create generators that depend on conditions:

```idris
genConditional : (condition : Bool) -> Fuel -> Gen MaybeEmpty (if condition then TypeA else TypeB)
genConditional = deriveGen
```

**Analysis:**
- The generator adapts based on the condition parameter
- Different generation strategies for each branch

## Exercises

### Exercise 1: Analyze a Signature

Given this signature:

```idris
genPair : Fuel -> (Fuel -> Gen MaybeEmpty a) => (Fuel -> Gen MaybeEmpty b) => Gen MaybeEmpty (a, b)
genPair = deriveGen
```

**Questions:**
1. What is the target type?
2. How many given parameters are there?
3. How many external generators are required?

**Solution:**
1. Target type: The pair type `(a, b)`
2. Given parameters: Only `Fuel` (the first parameter)
3. External generators: 2 (one for type `a`, one for type `b`)

**Explanation:** The signature specifies that generators for both `a` and `b` must be provided externally via auto-implicit arguments (`=>`).

### Exercise 2: Fix an Invalid Signature

The following signature is invalid. Identify the problem and fix it:

```idris
-- Invalid signature
genInvalid : Nat -> Gen MaybeEmpty List
genInvalid = deriveGen
```

**Problems identified:**
1. Missing `Fuel` parameter
2. `List` is not a concrete type (it needs type parameters)

**Fixed signature:**
```idris
-- Option 1: With external generator for element type
genList1 : Fuel -> (Fuel -> Gen MaybeEmpty a) => Gen MaybeEmpty (List a)
genList1 = deriveGen

-- Option 2: With specific element type
genList2 : Fuel -> Gen MaybeEmpty (List Nat)
genList2 = deriveGen

-- Option 3: Generating both length and contents
genList3 : Fuel -> Gen MaybeEmpty (n : Nat ** Vect n String)
genList3 = deriveGen
```

### Exercise 3: Create a Custom Signature

Design a generator signature for a type `Matrix : Nat -> Nat -> Type -> Type` that:
- Takes rows and columns as parameters
- Uses an external generator for the element type
- Returns a generator for `Matrix rows cols elem`

**Solution:**
```idris
genMatrix : (rows : Nat) -> (cols : Nat) ->
           (Fuel -> Gen MaybeEmpty elem) =>
           Fuel -> Gen MaybeEmpty (Matrix rows cols elem)
genMatrix = deriveGen
```

**Analysis:**
- Given parameters: `rows`, `cols`
- External generator: For element type `elem`
- Target type: `Matrix rows cols elem`

### Exercise 4: Advanced Signature Design

Create a generator signature for a type that:
- Generates a random size for a data structure
- Uses the generated size to create the structure
- Allows custom generation of internal elements

**Solution:**
```idris
genAdvanced : Fuel ->
            (Fuel -> Gen MaybeEmpty elem) =>
            Gen MaybeEmpty (size : Nat ** DataStructure size elem)
genAdvanced = deriveGen
```

### Exercise 5: Error Analysis

Why would this signature cause an error?

```idris
genProblematic : Fuel -> (x : Nat) -> Gen MaybeEmpty (Vect x String)
genProblematic = deriveGen
```

**Solution:**
This signature is actually valid! It creates a generator that:
- Takes `Fuel` and a specific length `x`
- Generates a `Vect` of that exact length
- Uses the built-in `String` generator

The signature is correct because `String` is a primitive type that DepTyCheck knows how to generate.

## Conclusion

Signature analysis is the foundation of DepTyCheck's automatic generation capabilities. By understanding how the system parses and validates generator signatures, you can:

- Write more effective generator signatures
- Debug signature-related errors
- Understand the limits and capabilities of automatic derivation
- Create complex generators for sophisticated data types

### Key Takeaways

1. **Signature as Blueprint**: Your generator signature serves as a precise blueprint that tells DepTyCheck exactly what to build.

2. **Parameter Classification**: DepTyCheck distinguishes between:
   - **Given parameters**: Provided by the user
   - **Generated parameters**: Created by the generator
   - **External generators**: Helper generators for sub-components

3. **Validation Rules**: The system enforces important rules:
   - Must start with `Fuel` parameter
   - Must return `Gen MaybeEmpty` type
   - All parameters must be properly named and typed

4. **Flexibility**: The signature system supports:
   - Dependent pairs for generating proofs
   - External generators for custom types
   - Implicit parameters with defaults
   - Complex nested dependencies

### Real-World Applications

Signature analysis enables powerful testing scenarios:

- **Property-based testing**: Generate complex inputs automatically
- **Regression testing**: Create comprehensive test suites
- **Fuzz testing**: Explore edge cases systematically
- **Integration testing**: Generate realistic data structures

### Best Practices

1. **Be explicit**: Use clear parameter names
2. **Consider dependencies**: Order parameters logically
3. **Use external generators**: For custom or complex types
4. **Test your signatures**: Verify they compile correctly
5. **Document complex signatures**: Add comments for clarity

### Error Handling and Debugging

When signature analysis fails, DepTyCheck provides helpful error messages:

```idris
-- Common error: Missing Fuel parameter
genBad1 : Gen MaybeEmpty MyType  -- Error: First argument must be Fuel

-- Common error: Invalid return type
genBad2 : Fuel -> MyType          -- Error: Must return Gen MaybeEmpty

-- Common error: Unused parameter
genBad3 : (unused : Nat) -> Fuel -> Gen MaybeEmpty MyType  -- Warning: Parameter unused
```

### Implementation Details

The signature analysis process involves several key functions:

1. **`checkTypeIsGen`**: Main parsing function in `src/Deriving/DepTyCheck/Gen.idr`
2. **`unPi`**: Splits function types into arguments and result
3. **`unDPairUnAlt`**: Analyzes dependent pairs
4. **`buildGenSignature`**: Constructs the final GenSignature record

These functions work together to transform your type signature into a structured blueprint that guides the entire code generation process.

In the next chapter, we'll explore how DepTyCheck uses these signatures to actually generate code and build the complete generator implementation.

## Summary

In this chapter, we've learned how DepTyCheck's signature analysis works:

- **Signature as Specification**: Your generator signature serves as a detailed specification that tells DepTyCheck exactly what to build
- **Structured Analysis**: The system parses signatures systematically, validating rules and extracting key information
- **Parameter Management**: DepTyCheck distinguishes between given, generated, and external parameters
- **Error Prevention**: The analysis catches common mistakes and provides helpful error messages
- **Flexible Design**: The system supports complex patterns including dependent pairs, external generators, and conditional generation

By mastering signature analysis, you can create powerful, type-safe generators that automatically handle complex data structures and dependencies.