# 9. Toy Example: Generating ASTs for a DSL

In previous tutorials, we learned how to create generators for simple data types and how to combine manual and automatic derivation. Now, let's apply these skills to a real-world scenario: generating **Abstract Syntax Trees (ASTs)** for a simple imperative programming language.

This tutorial is based on **PIL (Primitive Imperative Language)**, a real example from the DepTyCheck repository.

## Our Goal

In this tutorial, you will build a complete AST generator for a simple imperative language. By the end, you will have:

1.  Defined expression and statement types for the language
2.  Created both automatic (`deriveGen`) and hand-written generators
3.  Generated valid random programs with control flow structures

You will see output like:
```text
Seq (Assign "x" (Lit 5)) (If (Add (Var "x") (Lit 3)) (Assign "y" (Lit 10)) Skip)
```

**Expected time:** 30-40 minutes

---

## Step 1: Define the Expression Language

Let's start with the foundation: arithmetic and logical expressions.

### Create a new file named `PILTutorial.idr`.

### Add the basic setup and expression type:

```idris
import Data.Fuel
import Data.List
import Deriving.DepTyCheck.Gen
import Test.DepTyCheck.Gen
import System.Random.Pure.StdGen

-- Arithmetic and logical expressions
data Expr : Type where
  Lit   : Nat -> Expr
  Var   : String -> Expr
  Add   : Expr -> Expr -> Expr
  Mul   : Expr -> Expr -> Expr
  And   : Expr -> Expr -> Expr
  Lt    : Expr -> Expr -> Expr

Show Expr where
  show (Lit l) = "Lit " ++ show l
  show (Var s) = "Var " ++ show s
  show (Add e1 e2) = "Add (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (Mul e1 e2) = "Mul (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (And e1 e2) = "And (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (Lt e1 e2) = "Lt (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
```

### Create a simple derived generator with a generator-helper for strings:

```idris
genVarName : Fuel -> Gen MaybeEmpty String
genVarName _ = elements ["x", "y", "z", "temp", "result", "counter"]

genExpr : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty Expr
genExpr = deriveGen
```

### Test it:

```idris
main : IO ()
main = do
  putStrLn "--- Generating random expressions ---"
  for_ (the (List Int) [1..5]) $ \_ => do
    Just e <- pick (genExpr @{genVarName} (limit 3))
      | Nothing => putStrLn "Generation failed"
    printLn e
```

### Build and run:

```bash
echo -e ':exec main' | rlwrap pack repl ./PILTutorial.idr
```

Expected output (will vary):
```
--- Generating random expressions ---
Lt (Mul (Lt (Var "x") (Var "temp")) (Add (Lit 3) (Lit 1))) (Add (Var "temp") (Lt (Var "result") (Lit 0)))
Lt (And (Var "counter") (And (Lit 2) (Var "y"))) (And (Lit 1) (Add (Lit 0) (Var "counter")))
And (Mul (And (Lit 0) (Lit 0)) (Lit 3)) (Lit 3)
Mul (Lit 2) (Var "z")
Add (Lit 0) (Add (And (Var "y") (Lit 2)) (And (Lit 2) (Var "counter")))
```

> [!NOTE]\
> `deriveGen` automatically handles the recursive structure of expressions. The `limit 3` fuel controls the maximum depth of nested expressions.

---

## Step 2: Add Statements and Control Flow

Now let's add statements that form complete programs.

### Add the statement type to your file:

```idris
-- Statements with control flow
data Stmt : Type where
  Skip   : Stmt
  Assign : String -> Expr -> Stmt
  Seq    : Stmt -> Stmt -> Stmt
  If     : Expr -> Stmt -> Stmt -> Stmt
  While  : Expr -> Stmt -> Stmt

Show Stmt where
  show Skip = "Skip"
  show (Assign s e) = "Assign " ++ show s ++ " (" ++ show e ++ ")"
  show (Seq s1 s2) = "Seq (" ++ show s1 ++ ") (" ++ show s2 ++ ")"
  show (If e1 s1 s2) = "If (" ++ show e1 ++ ") (" ++ show s1 ++ ") (" ++ show s2 ++ ")"
  show (While e1 s1) = "While (" ++ show e1 ++ ") (" ++ show s1 ++ ")"
```

### Create a hand-written generator with explicit fuel control:

```idris
genStmt : Fuel -> Gen MaybeEmpty Stmt
genStmt Dry = pure Skip  -- Base case: only non-recursive constructors
genStmt (More f) = frequency
  [ (1, pure Skip)
  , (5, Assign <$> genVarName (More f) <*> genExpr @{genVarName} (More f))
  , (3, Seq <$> genStmt f <*> genStmt f)
  , (2, If  <$> genExpr @{genVarName} (More f) <*> genStmt f <*> genStmt f)
  , (2, While <$> genExpr @{genVarName} (More f) <*> genStmt f)
  ]
```

> [!NOTE]\
> - `genStmt Dry = pure Skip` ensures termination when fuel is exhausted
> - `genStmt f` (less fuel) in recursive calls controls program size
> - `frequency` weights make simple statements more common than complex ones

### Test the statement generator:

```idris
main_stmt : IO ()
main_stmt = do
  putStrLn "--- Generating random statements ---"
  for_ (the (List Int) [1..5]) $ \_ => do
    Just s <- pick (genStmt (limit 4))
      | Nothing => putStrLn "Generation failed"
    printLn s
```

Try to run `main_stmt`

```bash
echo -e ':exec main_stmt' | rlwrap pack repl ./PILTutorial.idr
```

Expected output:
```
--- Generating random statements ---
Assign "counter" (Lt (Lit 0) (Lit 4))
Assign "x" (Lt (Mul (Lt (Var "temp") (Lit 1)) (Lit 2)) (Lt (Var "counter") (And (Add (Var "y") (Lit 2)) (And (Var "counter") (Lit 2)))))
Assign "y" (And (Add (Mul (Var "x") (Var "temp")) (Var "temp")) (And (Mul (Mul (Var "y") (Lit 3)) (Lt (Var "counter") (Lit 2))) (Var "result")))
If (Lt (Mul (And (Lt (Lit 4) (Var "z")) (Add (Lit 1) (Var "x"))) (Mul (Mul (Var "x") (Var "y")) (Add (Lit 0) (Lit 0)))) (And (Lt (Add (Lit 3) (Lit 0)) (Mul (Lit 0) (Var "counter"))) (Add (Var "z") (Var "temp")))) (Assign "counter" (And (Mul (And (Var "z") (Lit 1)) (Var "result")) (Var "result"))) (If (Lt (Mul (And (Var "z") (Var "counter")) (Lit 0)) (Add (Lit 0) (Mul (Lit 3) (Lit 3)))) (If (Mul (Mul (Lit 0) (Var "result")) (And (Lit 1) (Var "temp"))) (While (Lt (Var "x") (Var "y")) (Skip)) (While (Lt (Var "result") (Var "temp")) (Skip))) (Assign "temp" (Lt (Mul (Lit 2) (Lit 1)) (Mul (Lit 0) (Var "counter")))))
Seq (Assign "result" (Var "z")) (While (Add (Add (Var "counter") (And (Lit 3) (Lit 2))) (Lt (And (Var "temp") (Lit 1)) (Var "temp"))) (Assign "y" (And (Lt (Var "counter") (Lit 1)) (Lt (Var "counter") (Var "temp")))))
```

---

## Step 3: Generate Complete Programs

Now let's generate complete programs with multiple statements.

### Define a Program type and generator:

```idris
-- A program is a list of statements
data Program = MkProgram (List Stmt)

Show Program where
  show (MkProgram lst) = "MkProgram " ++ show lst

genProgram : (n : Nat) -> Fuel -> Gen MaybeEmpty Program
genProgram n fuel = MkProgram <$> listOf {length=pure n} (genStmt fuel)
```

### Test program generation:

```idris
main_program : IO ()
main_program = do
  putStrLn "--- Generating a random program (5 statements) ---"
  Just prog <- pick (genProgram 5 (limit 3))
    | Nothing => putStrLn "Generation failed"
  printLn prog
```

Try to run

```bash
echo -e ':exec main_program' | rlwrap pack repl ./PILTutorial.idr
```

Expected output:
```
--- Generating a random program (5 statements) ---
MkProgram [Seq (While (Add (Lit 1) (And (Lit 1) (Var "x"))) (While (Var "x") (Skip))) (Assign "temp" (And (And (Var "temp") (Var "y")) (Lit 1))), If (And (Add (Add (Var "x") (Lit 0)) (Lit 1)) (Lit 2)) (Assign "result" (Lt (Lt (Lit 2) (Var "temp")) (Mul (Var "y") (Var "y")))) (While (Var "temp") (Seq (Skip) (Skip))), While (Mul (Var "result") (Mul (Lit 1) (Add (Var "y") (Lit 1)))) (Assign "counter" (Lt (And (Lit 1) (Var "result")) (Lit 0))), Seq (If (And (And (Lit 1) (Var "result")) (Mul (Lit 0) (Lit 1))) (If (Lit 1) (Skip) (Skip)) (While (Lit 0) (Skip))) (If (Mul (Add (Var "x") (Lit 1)) (And (Lit 1) (Var "counter"))) (While (Add (Lit 1) (Lit 1)) (Skip)) (Assign "y" (Add (Lit 1) (Lit 0)))), Assign "temp" (Add (Add (Lit 1) (And (Var "y") (Var "z"))) (And (Lit 1) (Lit 3)))]
```

> [!NOTE]\
> `listOf {length=pure n} gen` runs the generator `n` times and collects results into a list.

---

## Step 4: Test Properties of Generated Programs

Let's verify that our generated programs have certain properties.

### Add property checking functions:

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

### Test properties:

```idris
main_properties : IO ()
main_properties = do
  putStrLn "--- Checking properties of generated programs ---"
  for_ (the (List Int) [1..10]) $ \_ => do
    Just prog <- pick (genProgram 3 (limit 3))
      | Nothing => putStrLn "Generation failed"

    let hasAnyAssign = Prelude.any {t=List} hasAssign (case prog of MkProgram stmts => stmts)
    let hasAnyLoop = Prelude.any {t=List} hasLoop (case prog of MkProgram stmts => stmts)
    let count = stmtCount prog

    putStrLn $ "Program with " ++ show count ++ " statements"
    putStrLn $ "  Has assignment: " ++ show hasAnyAssign
    putStrLn $ "  Has loop: " ++ show hasAnyLoop
    putStrLn ""
```

Try to run

```bash
echo -e ':exec main_properties' | rlwrap pack repl ./PILTutorial.idr
```

A sample of the output:
```
--- Checking properties of generated programs ---
Program with 3 statements
  Has assignment: True
  Has loop: False

Program with 3 statements
  Has assignment: True
  Has loop: True

Program with 3 statements
  Has assignment: True
  Has loop: False
...
```

> [!NOTE]\
> You can use these property checks to ensure your generated programs meet certain criteria for testing compilers or interpreters.

---

## Next Steps

Now that you can generate complex ASTs, you're ready for many other applications:

*   **Test an interpreter:** Use your generated PIL programs to test a language interpreter with property-based testing.
*   **Add more language features:** Extend the language with functions, arrays, or I/O operations.
*   **Integrate custom generators:** Continue to **[Mixing Manual and Automatic](t06-mixing-manual-and-automatic.md)** to see how `deriveGen` discovers and uses your custom generators.
*   **Control distribution:** Continue to **[Derivation Tuning](t10-derivation-tuning.md)** to learn how to fine-tune constructor probabilities for more realistic program distributions.
*   **Understand the internals:** Continue to **[Under the Hood](t11-under-the-hood-a-derivegen-like-macro.md)** to see how `deriveGen` works internally.

The complete `PILTutorial.idr` file is available for reference. You can find it in the DepTyCheck examples or build it step-by-step following this tutorial.

