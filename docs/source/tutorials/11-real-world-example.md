# 11. Real-World Example: Generating ASTs for a DSL

In previous tutorials, we learned how to create generators for simple data types and how to combine manual and automatic derivation. Now, let's apply these skills to a real-world scenario: generating **Abstract Syntax Trees (ASTs)** for a simple imperative programming language.

This tutorial is based on **PIL (Primitive Imperative Language)**, a real example from the DepTyCheck repository.

## Our Goal

In this tutorial, you will build a complete AST generator for a simple imperative language. By the end, you will have:

1.  Defined expression and statement types for the language
2.  Created both automatic (`deriveGen`) and hand-written generators
3.  Generated valid random programs with control flow structures

You will see output like:
```idris
Seq (Assign "x" (Lit 5)) (If (Add (Var "x") (Lit 3)) (Assign "y" (Lit 10)) Skip) : Stmt
```

**Expected time:** 30-40 minutes

---

## Step 1: Define the Expression Language

Let's start with the foundation: arithmetic and logical expressions.

1.  **Create a new file** named `PILTutorial.idr`.

2.  **Add the basic setup and expression type:**

    ```idris
    module PILTutorial

    %language ElabReflection

    import Data.Fuel
    import Deriving.DepTyCheck.Gen
    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Runner

    -- Types in our language
    data Type' = IntType | BoolType

    -- Arithmetic and logical expressions
    data Expr : Type where
      Lit   : Nat -> Expr
      Var   : String -> Expr
      Add   : Expr -> Expr -> Expr
      Mul   : Expr -> Expr -> Expr
      And   : Expr -> Expr -> Expr
      Lt    : Expr -> Expr -> Expr
    ```

3.  **Create a simple derived generator:**

    ```idris
    genExpr : Fuel -> Gen MaybeEmpty Expr
    genExpr = deriveGen
    ```

4.  **Test it:**

    ```idris
    main : IO ()
    main = do
      putStrLn "--- Generating random expressions ---"
      replicate 5 $ do
        Just e <- pick1 (genExpr (limit 3))
          | Nothing => putStrLn "Generation failed"
        printLn e
    ```

5.  **Build and run:**
    ```bash
    pack build PILTutorial
    pack exec PILTutorial
    ```

    Expected output (will vary):
    ```
    --- Generating random expressions ---
    Add (Lit 2) (Var "x")
    Lit 5
    Mul (Add (Lit 1) (Lit 2)) (Var "y")
    Var "temp"
    Lt (Lit 3) (Lit 7)
    ```

🔍 **Notice:** `deriveGen` automatically handles the recursive structure of expressions. The `limit 3` fuel controls the maximum depth of nested expressions.

---

## Step 2: Add Statements and Control Flow

Now let's add statements that form complete programs.

1.  **Add the statement type** to your file:

    ```idris
    -- Statements with control flow
    data Stmt : Type where
      Skip   : Stmt
      Assign : String -> Expr -> Stmt
      Seq    : Stmt -> Stmt -> Stmt
      If     : Expr -> Stmt -> Stmt -> Stmt
      While  : Expr -> Stmt -> Stmt
    ```

2.  **Create a hand-written generator** with explicit fuel control:

    ```idris
    genStmt : Fuel -> Gen MaybeEmpty Stmt
    genStmt Dry = pure Skip  -- Base case: only non-recursive constructors
    genStmt (More f) = frequency
      [ (1, pure Skip)
      , (5, Assign <$> elements ["x", "y", "z", "temp"] <*> genExpr (More f))
      , (3, Seq <$> genStmt f <*> genStmt f)
      , (2, If  <$> genExpr (More f) <*> genStmt f <*> genStmt f)
      , (2, While <$> genExpr (More f) <*> genStmt f)
      ]
    ```

    🔍 **Notice:**
    -   `genStmt Dry = pure Skip` ensures termination when fuel is exhausted
    -   `genStmt f` (less fuel) in recursive calls controls program size
    -   `frequency` weights make simple statements more common than complex ones

3.  **Test the statement generator:**

    ```idris
    main_stmt : IO ()
    main_stmt = do
      putStrLn "--- Generating random statements ---"
      replicate 5 $ do
        Just s <- pick1 (genStmt (limit 4))
          | Nothing => putStrLn "Generation failed"
        printLn s

    -- Update main to call this
    main : IO ()
    main = main_stmt
    ```

    Expected output:
    ```
    --- Generating random statements ---
    Assign "x" (Lit 5)
    Seq Skip (Assign "y" (Add (Var "x") (Lit 3)))
    If (Lt (Var "x") (Lit 10)) (Assign "y" (Lit 1)) Skip
    While (Var "x") Skip
    Seq (Assign "temp" (Lit 7)) (If (Var "x") Skip Skip)
    ```

---

## Step 3: Hand-Written Generator for Expressions

The automatic generator works, but it generates random variable names. Let's create a custom expression generator with controlled variable names.

1.  **Add a custom expression generator:**

    ```idris
    genVarName : Gen MaybeEmpty String
    genVarName = elements ["x", "y", "z", "temp", "result", "counter"]

    genExprManual : Fuel -> Gen MaybeEmpty Expr
    genExprManual Dry = oneOf
      [ Lit <$> choose (0, 100)
      , Var <$> genVarName
      ]
    genExprManual (More f) = frequency
      [ (3, Lit <$> choose (0, 100))
      , (2, Var <$> genVarName)
      , (2, Add <$> genExprManual f <*> genExprManual f)
      , (2, Mul <$> genExprManual f <*> genExprManual f)
      , (1, And <$> genExprManual f <*> genExprManual f)
      , (1, Lt  <$> genExprManual f <*> genExprManual f)
      ]
    ```

2.  **Update `genStmt` to use the manual expression generator:**

    ```idris
    genStmtManual : Fuel -> Gen MaybeEmpty Stmt
    genStmtManual Dry = pure Skip
    genStmtManual (More f) = frequency
      [ (1, pure Skip)
      , (5, Assign <$> genVarName <*> genExprManual (More f))
      , (3, Seq <$> genStmtManual f <*> genStmtManual f)
      , (2, If  <$> genExprManual (More f) <*> genStmtManual f <*> genStmtManual f)
      , (2, While <$> genExprManual (More f) <*> genStmtManual f)
      ]
    ```

3.  **Test the manual generator:**

    ```idris
    main_manual : IO ()
    main_manual = do
      putStrLn "--- Generating with manual expression generator ---"
      replicate 5 $ do
        Just s <- pick1 (genStmtManual (limit 4))
          | Nothing => putStrLn "Generation failed"
        printLn s

    main : IO ()
    main = main_manual
    ```

    Expected output:
    ```
    --- Generating with manual expression generator ---
    Assign "x" (Lit 42)
    Seq (Assign "y" (Add (Var "x") (Lit 5))) (Assign "temp" (Lit 10))
    If (Lt (Var "x") (Var "y")) (Assign "result" (Lit 1)) Skip
    While (Lt (Var "counter") (Lit 10)) (Assign "counter" (Add (Var "counter") (Lit 1)))
    Seq Skip (Assign "z" (Mul (Lit 3) (Lit 7)))
    ```

🔍 **Notice:** The manual generator gives you full control over variable names and expression distribution.

---

## Step 4: Generate Complete Programs

Now let's generate complete programs with multiple statements.

1.  **Define a Program type and generator:**

    ```idris
    -- A program is a list of statements
    data Program = MkProgram (List Stmt)

    genProgram : (n : Nat) -> Fuel -> Gen MaybeEmpty Program
    genProgram n fuel = MkProgram <$> listOf n (genStmtManual fuel)
    ```

2.  **Test program generation:**

    ```idris
    main_program : IO ()
    main_program = do
      putStrLn "--- Generating a random program (5 statements) ---"
      Just prog <- pick1 (genProgram 5 (limit 3))
        | Nothing => putStrLn "Generation failed"
      printLn prog

    main : IO ()
    main = main_program
    ```

    Expected output:
    ```
    --- Generating a random program (5 statements) ---
    MkProgram
      [ Assign "x" (Lit 5)
      , If (Lt (Var "x") (Lit 10)) (Assign "y" (Lit 10)) Skip
      , Seq Skip (Assign "z" (Lit 7))
      , While (Lt (Var "counter") (Lit 10)) (Assign "counter" (Add (Var "counter") (Lit 1)))
      , Assign "temp" (Mul (Lit 2) (Lit 3))
      ]
    ```

🔍 **Notice:** `listOf n gen` runs the generator `n` times and collects results into a list.

---

## Step 5: Add Type Safety (Optional Advanced Step)

For more realistic languages, we want to ensure type correctness. Let's add typed expressions.

1.  **Define typed expressions:**

    ```idris
    -- Typed expressions (guaranteed type-correct by construction)
    data TypedExpr : Type' -> Type where
      IntLit  : Nat -> TypedExpr IntType
      BoolLit : Bool -> TypedExpr BoolType
      IntVar  : String -> TypedExpr IntType
      BoolVar : String -> TypedExpr BoolType
      IntAdd  : TypedExpr Inttype -> TypedExpr IntType -> TypedExpr IntType
      IntMul  : TypedExpr IntType -> TypedExpr IntType -> TypedExpr IntType
      BoolAnd : TypedExpr BoolType -> TypedExpr BoolType -> TypedExpr BoolType
      IntLt   : TypedExpr IntType -> TypedExpr IntType -> TypedExpr BoolType
    ```

2.  **Create a typed expression generator:**

    ```idris
    genTypedExpr : (t : Type') -> Fuel -> Gen MaybeEmpty (TypedExpr t)
    genTypedExpr IntType fuel = frequency
      [ (2, IntLit <$> choose (0, 100))
      , (2, IntVar <$> elements ["x", "y", "z", "n"])
      , (1, IntAdd <$> genTypedExpr IntType fuel <*> genTypedExpr IntType fuel)
      , (1, IntMul <$> genTypedExpr IntType fuel <*> genTypedExpr IntType fuel)
      ]
    genTypedExpr BoolType fuel = frequency
      [ (2, BoolLit <$> elements [True, False])
      , (2, BoolVar <$> elements ["flag", "done", "ready"])
      , (1, BoolAnd <$> genTypedExpr BoolType fuel <*> genTypedExpr BoolType fuel)
      , (1, IntLt <$> genTypedExpr IntType fuel <*> genTypedExpr IntType fuel)
      ]
    ```

3.  **Test typed generation:**

    ```idris
    main_typed : IO ()
    main_typed = do
      putStrLn "--- Generating typed integer expressions ---"
      replicate 3 $ do
        Just e <- pick1 (genTypedExpr IntType (limit 3))
          | Nothing => putStrLn "Failed"
        printLn e

      putStrLn "\n--- Generating typed boolean expressions ---"
      replicate 3 $ do
        Just e <- pick1 (genTypedExpr BoolType (limit 3))
          | Nothing => putStrLn "Failed"
        printLn e

    main : IO ()
    main = main_typed
    ```

    Expected output:
    ```
    --- Generating typed integer expressions ---
    IntAdd (IntLit 5) (IntVar "x")
    IntMul (IntLit 3) (IntLit 7)
    IntVar "y"

    --- Generating typed boolean expressions ---
    BoolAnd (BoolLit True) (IntLt (IntVar "x") (IntLit 10))
    BoolVar "flag"
    IntLt (IntAdd (IntVar "n") (IntLit 1)) (IntLit 100)
    ```

🔍 **Notice:** The type system guarantees that `genTypedExpr IntType` only produces integer expressions, and `genTypedExpr BoolType` only produces boolean expressions.

---

## Step 6: Test Properties of Generated Programs

Let's verify that our generated programs have certain properties.

1.  **Add property checking functions:**

    ```idris
    -- Check if a statement contains an assignment
    hasAssign : Stmt -> Bool
    hasAssign Skip = False
    hasAssign (Assign _ _) = True
    hasAssign (Seq s1 s2) = hasAssign s1 || hasAssign s2
    hasAssign (If _ s1 s2) = hasAssign s1 || hasAssign s2
    hasAssign (While _ s) = hasAssign s

    -- Count statements in a program
    stmtCount : Program -> Nat
    stmtCount (MkProgram stmts) = length stmts

    -- Check if program has a loop
    hasLoop : Stmt -> Bool
    hasLoop Skip = False
    hasLoop (Assign _ _) = False
    hasLoop (Seq s1 s2) = hasLoop s1 || hasLoop s2
    hasLoop (If _ s1 s2) = hasLoop s1 || hasLoop s2
    hasLoop (While _ _) = True
    ```

2.  **Test properties:**

    ```idris
    main_properties : IO ()
    main_properties = do
      putStrLn "--- Checking properties of generated programs ---"
      replicate 10 $ do
        Just prog <- pick1 (genProgram 3 (limit 3))
          | Nothing => putStrLn "Generation failed"

        let hasAnyAssign = any hasAssign (case prog of MkProgram stmts => stmts)
        let hasAnyLoop = any hasLoop (case prog of MkProgram stmts => stmts)
        let count = stmtCount prog

        putStrLn $ "Program with " ++ show count ++ " statements"
        putStrLn $ "  Has assignment: " ++ show hasAnyAssign
        putStrLn $ "  Has loop: " ++ show hasAnyLoop
        putStrLn ""

    main : IO ()
    main = main_properties
    ```

    Expected output:
    ```
    --- Checking properties of generated programs ---
    Program with 3 statements
      Has assignment: True
      Has loop: False

    Program with 3 statements
      Has assignment: True
      Has loop: True

    Program with 3 statements
      Has assignment: False
      Has loop: False
    ...
    ```

🔍 **Notice:** You can use these property checks to ensure your generated programs meet certain criteria for testing compilers or interpreters.

---

## Next Steps

Now that you can generate complex ASTs, you're ready for real-world applications:

*   **Test an interpreter:** Use your generated PIL programs to test a language interpreter with property-based testing.
*   **Add more language features:** Extend the language with functions, arrays, or I/O operations.
*   **Integrate custom generators:** Continue to **[Mixing Manual and Automatic](09-mixing-manual-and-automatic.md)** to see how `deriveGen` discovers and uses your custom generators.
*   **Control distribution:** Continue to **[Derivation Tuning](07-derivation-tuning.md)** to learn how to fine-tune constructor probabilities for more realistic program distributions.
*   **Understand the internals:** Continue to **[Under the Hood](08-under-the-hood-a-derivegen-like-macro.md)** to see how `deriveGen` works internally.

The complete `PILTutorial.idr` file is available for reference. You can find it in the DepTyCheck examples or build it step-by-step following this tutorial.

