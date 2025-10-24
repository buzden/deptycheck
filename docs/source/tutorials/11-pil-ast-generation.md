# Mastering Domain Languages: Generating ASTs for DSLs

## What We'll Accomplish
In this tutorial, we'll learn how to generate complex abstract syntax trees (ASTs) for domain-specific languages. By the end, you'll:
- Define a simple imperative language AST
- Use `deriveGen` to generate valid programs
- Control program complexity with Fuel
- Have a working DSL AST generator

## Prerequisites
Before we begin, make sure you have:
- Completed the "Generate Test Data for a Simple Type with `deriveGen`" tutorial
- Basic understanding of abstract syntax trees
- Idris 2 installed and DepTyCheck available in your project

## Step 1: Create a Simple Expression Language

Let's start with a basic arithmetic expression language. Create a new file called `DSLLearning.idr`:

```idris
module DSLLearning

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.Nat

%language ElabReflection

data Expr : Type where
  Lit : Nat -> Expr
  Var : String -> Expr
  Add : Expr -> Expr -> Expr
  Mul : Expr -> Expr -> Expr

genExpr : Fuel -> Gen MaybeEmpty Expr
genExpr fuel = deriveGen

main : IO ()
main = do
  putStrLn "Generating simple expressions:"
  let results = take 5 $ unGen1 (limit 5) genExpr
  traverse_ (putStrLn . show) results
```

**Expected result**: You should see arithmetic expressions like `Add (Lit 3) (Var "x")`.

**What to notice**: The generator creates syntactically valid expressions.

## Step 2: Extend to a Full Imperative Language

Now let's extend our language to include statements and control flow:

```idris
-- Add to your existing file
data Stmt : Type where
  Skip : Stmt
  Assign : String -> Expr -> Stmt
  If : Expr -> Stmt -> Stmt -> Stmt
  While : Expr -> Stmt -> Stmt
  Seq : Stmt -> Stmt -> Stmt

genStmt : Fuel -> Gen MaybeEmpty Stmt
genStmt fuel = deriveGen

testStmt : IO ()
testStmt = do
  putStrLn "Generating imperative statements:"
  let smallStmts = take 3 $ unGen1 (limit 3) genStmt
  let largeStmts = take 3 $ unGen1 (limit 5) genStmt
  
  putStrLn "Small statements:"
  traverse_ (putStrLn . show) smallStmts
  
  putStrLn "\nLarge statements:"
  traverse_ (putStrLn . show) largeStmts

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testStmt
```

**Expected result**: You should see imperative programs with assignments, conditionals, and loops.

**What to notice**: DepTyCheck handles the complex recursion in statement generation.

## Step 3: Create a Typed Language

Let's add type information to our language:

```idris
-- Add to your existing file
data Type = IntType | BoolType

data TypedExpr : Type -> Type where
  IntLit : Nat -> TypedExpr IntType
  BoolLit : Bool -> TypedExpr BoolType
  IntVar : String -> TypedExpr IntType
  BoolVar : String -> TypedExpr BoolType
  TypedAdd : TypedExpr IntType -> TypedExpr IntType -> TypedExpr IntType
  TypedEq : TypedExpr a -> TypedExpr a -> TypedExpr BoolType

genTypedExpr : (t : Type) -> Fuel -> Gen MaybeEmpty (TypedExpr t)
genTypedExpr t fuel = deriveGen

testTypedExpr : IO ()
testTypedExpr = do
  putStrLn "Generating typed expressions:"
  let intExprs = take 3 $ unGen1 (limit 5) (genTypedExpr IntType (limit 5))
  let boolExprs = take 3 $ unGen1 (limit 5) (genTypedExpr BoolType (limit 5))
  
  putStrLn "Integer expressions:"
  traverse_ (putStrLn . show) intExprs
  
  putStrLn "\nBoolean expressions:"
  traverse_ (putStrLn . show) boolExprs

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testTypedExpr
```

**Expected result**: You should see type-correct expressions.

**What to notice**: The generator respects the type constraints automatically.

## Step 4: Create a Simple Function Language

Let's extend our language to include functions:

```idris
-- Add to your existing file
data FuncDef : Type where
  MkFunc : (name : String) -> (args : List (String, Type)) -> 
           (body : Stmt) -> (returnType : Type) -> FuncDef

data Program : Type where
  MkProgram : (funcs : List FuncDef) -> (main : Stmt) -> Program

genFuncDef : Fuel -> Gen MaybeEmpty FuncDef
genFuncDef fuel = deriveGen

genProgram : Fuel -> Gen MaybeEmpty Program
genProgram fuel = deriveGen

testProgram : IO ()
testProgram = do
  putStrLn "Generating programs with functions:"
  let results = take 2 $ unGen1 (limit 5) genProgram
  traverse_ (putStrLn . show) results

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testProgram
```

**Expected result**: You should see complete programs with function definitions.

**What to notice**: DepTyCheck handles the complex nesting of language constructs.

## What We Accomplished

Congratulations! We've successfully learned how to generate complex ASTs:
- Created several DSLs with increasing complexity
- Generated type-correct expressions and statements
- Extended the language to include functions and programs
- Used `deriveGen` to automatically generate valid programs

You now have the skills to generate test data for compilers, interpreters, and language processors.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Testing Language Interpreters with Generated Programs
- How-to: Creating Custom Generators for Language Extensions
- Explanation: How DepTyCheck Handles Complex Recursive Types

Or experiment by creating your own domain-specific languages and see how DepTyCheck handles their unique structures.