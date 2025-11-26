# Mastering Complex Types: Generating GADT Constructors

## What We'll Accomplish
In this tutorial, we'll learn how to generate data for Generalized Algebraic Data Types (GADTs) that maintain complex type-level constraints. By the end, you'll:
- Create a GADT with precise type indexing
- Use `deriveGen` to generate type-correct GADT terms
- Understand how DepTyCheck handles type constraints automatically
- Have a working example demonstrating GADT generation

## Prerequisites
Before we begin, make sure you have:
- Completed the "Generate Test Data for a Simple Type with `deriveGen`" tutorial
- Basic understanding of dependent types and GADTs
- Idris 2 installed and DepTyCheck available in your project

## Step 1: Create a Simple GADT

Let's start by creating a GADT that represents typed expressions. Create a new file called `GADTLearning.idr`:

```idris
module GADTLearning

import Data.Fuel
import Test.DepTyCheck.Gen

%language ElabReflection

data ExprType = IntType | BoolType

data TypedExpr : ExprType -> Type where
  IntLit : Int -> TypedExpr IntType
  BoolLit : Bool -> TypedExpr BoolType
  Add : TypedExpr IntType -> TypedExpr IntType -> TypedExpr IntType
  And : TypedExpr BoolType -> TypedExpr BoolType -> TypedExpr BoolType

genTypedExpr : (t : ExprType) -> Fuel -> Gen MaybeEmpty (TypedExpr t)
genTypedExpr t fuel = deriveGen

main : IO ()
main = do
  putStrLn "Generating typed expressions:"
  let intExprs = take 3 $ unGen1 (limit 5) (genTypedExpr IntType (limit 5))
  let boolExprs = take 3 $ unGen1 (limit 5) (genTypedExpr BoolType (limit 5))
  
  putStrLn "Int expressions:"
  traverse_ (putStrLn . show) intExprs
  
  putStrLn "\nBool expressions:"
  traverse_ (putStrLn . show) boolExprs
```

**Expected result**: You should see integer expressions (like `IntLit 5` or `Add (IntLit 1) (IntLit 2)`) and boolean expressions (like `BoolLit True` or `And (BoolLit True) (BoolLit False)`).

**What to notice**: The generator produces expressions that match the specified type exactly.

## Step 2: Create a More Complex GADT

Now let's create a GADT with more complex type dependencies:

```idris
-- Add to your existing file
data NatExpr : Nat -> Type where
  ZeroExpr : NatExpr 0
  SuccExpr : NatExpr n -> NatExpr (S n)
  AddExpr : NatExpr m -> NatExpr n -> NatExpr (m + n)

genNatExpr : (n : Nat) -> Fuel -> Gen MaybeEmpty (NatExpr n)
genNatExpr n fuel = deriveGen

testNatExpr : IO ()
testNatExpr = do
  putStrLn "Generating Nat expressions:"
  let zeroExprs = take 2 $ unGen1 (limit 3) (genNatExpr 0 (limit 3))
  let succExprs = take 2 $ unGen1 (limit 3) (genNatExpr 2 (limit 3))
  let addExprs = take 2 $ unGen1 (limit 3) (genNatExpr 3 (limit 3))
  
  putStrLn "Zero expressions:"
  traverse_ (putStrLn . show) zeroExprs
  
  putStrLn "\nSucc expressions:"
  traverse_ (putStrLn . show) succExprs
  
  putStrLn "\nAdd expressions:"
  traverse_ (putStrLn . show) addExprs

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testNatExpr
```

**Expected result**: You should see expressions that correctly represent the specified natural numbers.

**What to notice**: The generator respects the type-level arithmetic constraints.

## Step 3: Handle Equality Constraints

Let's create a GADT that requires equality constraints:

```idris
-- Add to your existing file
data EqualExpr : (a : Type) -> (b : Type) -> Type where
  EqExpr : (x : a) -> (y : a) -> EqualExpr a a

genEqualExpr : (a : Type) -> (b : Type) -> Fuel -> Gen MaybeEmpty (EqualExpr a b)
genEqualExpr a b fuel = deriveGen

testEqualExpr : IO ()
testEqualExpr = do
  putStrLn "Testing equality constraints:"
  
  -- This should work - same type
  let sameTypeExprs = take 2 $ unGen1 (limit 3) (genEqualExpr Nat Nat (limit 3))
  putStrLn "Same type expressions:"
  traverse_ (putStrLn . show) sameTypeExprs
  
  -- This might produce Nothing due to type mismatch
  let diffTypeExprs = take 2 $ unGen1 (limit 3) (genEqualExpr Nat Bool (limit 3))
  putStrLn "\nDifferent type expressions:"
  traverse_ (putStrLn . maybe "No valid expression" show) diffTypeExprs

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testEqualExpr
```

**Expected result**: You should see expressions when types match, and potentially no expressions when types differ.

**What to notice**: DepTyCheck handles the equality constraint automatically.

## Step 4: Advanced GADT with Multiple Constraints

Let's create a more sophisticated GADT with multiple constraints:

```idris
-- Add to your existing file
data ComplexExpr : (input : Type) -> (output : Type) -> Type where
  Identity : (x : a) -> ComplexExpr a a
  ConstExpr : (x : a) -> (y : b) -> ComplexExpr a b
  Compose : ComplexExpr b c -> ComplexExpr a b -> ComplexExpr a c

genComplexExpr : (input : Type) -> (output : Type) -> Fuel -> Gen MaybeEmpty (ComplexExpr input output)
genComplexExpr input output fuel = deriveGen

testComplexExpr : IO ()
testComplexExpr = do
  putStrLn "Testing complex GADT:"
  
  let identityExprs = take 2 $ unGen1 (limit 3) (genComplexExpr Nat Nat (limit 3))
  putStrLn "Identity expressions:"
  traverse_ (putStrLn . show) identityExprs
  
  let constExprs = take 2 $ unGen1 (limit 3) (genComplexExpr Nat Bool (limit 3))
  putStrLn "\nConst expressions:"
  traverse_ (putStrLn . show) constExprs
  
  let composeExprs = take 2 $ unGen1 (limit 3) (genComplexExpr Nat Int (limit 3))
  putStrLn "\nCompose expressions:"
  traverse_ (putStrLn . show) composeExprs

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testComplexExpr
```

**Expected result**: You should see complex expressions that respect all type constraints.

**What to notice**: DepTyCheck handles the complex type matching required for composition.

## What We Accomplished

Congratulations! We've successfully learned how to generate data for complex GADTs:
- Created GADTs with various type constraints
- Used `deriveGen` to automatically generate type-correct terms
- Handled equality constraints and complex type dependencies

You now have the skills to generate test data for even the most complex dependent types.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Generating Sorted Lists with Dependent Types
- How-to: Testing Functions with Complex Type Signatures
- Explanation: How DepTyCheck Resolves Type Constraints

Or experiment by creating your own GADTs with custom constraints and see how DepTyCheck handles them.