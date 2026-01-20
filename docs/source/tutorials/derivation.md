# Mastering Automatic Generation: The Power of `deriveGen`

## What We'll Accomplish
In this tutorial, we'll explore the core feature of DepTyCheck: automatic generator derivation. By the end, you'll:
- Understand when and how to use `deriveGen`
- Learn best practices for automatic derivation
- Handle complex type scenarios with derivation
- Have comprehensive knowledge of derivation capabilities

## Prerequisites
Before we begin, make sure you have:
- Completed the basic DepTyCheck tutorials
- Experience with Idris data types
- Idris 2 installed and DepTyCheck available in your project

## Step 1: Basic Derivation Patterns

Let's start with the most common derivation patterns. Create `DerivationBasics.idr`:

```idris
module DerivationBasics

import Data.Fuel
import Test.DepTyCheck.Gen

%language ElabReflection

-- Simple ADT
data Color = Red | Green | Blue

-- Recursive type
data NatList = Nil | Cons Nat NatList

-- Parameterized type
data Box a = MkBox a

genColor : Fuel -> Gen MaybeEmpty Color
genColor = deriveGen

genNatList : Fuel -> Gen MaybeEmpty NatList
genNatList = deriveGen

genBox : Fuel -> Gen MaybeEmpty (Box Nat)
genBox = deriveGen

main : IO ()
main = do
  putStrLn "Testing basic derivation:"
  let colors = take 3 $ unGen1 (limit 5) genColor
  let lists = take 3 $ unGen1 (limit 5) genNatList
  let boxes = take 3 $ unGen1 (limit 5) genBox
  
  putStrLn "Colors:"
  traverse_ (putStrLn . show) colors
  
  putStrLn "\nLists:"
  traverse_ (putStrLn . show) lists
  
  putStrLn "\nBoxes:"
  traverse_ (putStrLn . show) boxes
```

**Expected result**: You should see various instances of all three types.

**What to notice**: `deriveGen` works consistently across different type structures.

## Step 2: Advanced Derivation Features

Now let's explore more advanced derivation scenarios:

```idris
-- Continue in DerivationBasics.idr

-- Dependent type
data Vector : Nat -> Type -> Type where
  VNil : Vector Z a
  VCons : a -> Vector n a -> Vector (S n) a

-- GADT
data Expr : Type -> Type where
  IntExpr : Int -> Expr Int
  BoolExpr : Bool -> Expr Bool
  AddExpr : Expr Int -> Expr Int -> Expr Int

genVector : (n : Nat) -> Fuel -> Gen MaybeEmpty (Vector n Nat)
genVector n = deriveGen

genExpr : (t : Type) -> Fuel -> Gen MaybeEmpty (Expr t)
genExpr t = deriveGen

testAdvanced : IO ()
testAdvanced = do
  putStrLn "Testing advanced derivation:"
  
  putStrLn "Vectors:"
  let vec3 = take 2 $ unGen1 (limit 5) (genVector 3 (limit 5))
  traverse_ (putStrLn . show) vec3
  
  putStrLn "\nExpressions:"
  let intExprs = take 2 $ unGen1 (limit 5) (genExpr Int (limit 5))
  let boolExprs = take 2 $ unGen1 (limit 5) (genExpr Bool (limit 5))
  
  putStrLn "Integer expressions:"
  traverse_ (putStrLn . show) intExprs
  
  putStrLn "\nBoolean expressions:"
  traverse_ (putStrLn . show) boolExprs

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testAdvanced
```

**Expected result**: You should see complex types with proper constraints.

**What to notice**: DepTyCheck handles dependent types and GADTs automatically.

## Step 3: Derivation with Constraints

Let's explore how derivation handles constraints and proofs:

```idris
-- Continue in DerivationBasics.idr

-- Type with constraints
data EvenList : Type where
  EvenNil : EvenList
  EvenCons : (x : Nat) -> (xs : EvenList) -> {auto prf : Even (length (toList xs) + 1)} -> EvenList

where
  toList : EvenList -> List Nat
  toList EvenNil = []
  toList (EvenCons x xs prf) = x :: toList xs
  
  length : List a -> Nat
  length [] = 0
  length (x :: xs) = 1 + length xs

genEvenList : Fuel -> Gen MaybeEmpty EvenList
genEvenList = deriveGen

testConstrained : IO ()
testConstrained = do
  putStrLn "Testing constrained derivation:"
  let results = take 3 $ unGen1 (limit 5) genEvenList
  traverse_ (putStrLn . show) results
  
  -- Verify the constraint
  putStrLn "\nVerifying constraints:"
  for_ results $ \list => do
    let len = length (toList list)
    putStrLn $ "List length: " ++ show len ++ ", Even: " ++ show (even len)

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testConstrained
```

**Expected result**: You should see lists that always have even lengths.

**What to notice**: The proof constraints are automatically satisfied.

## What We Accomplished

Congratulations! We've explored the full power of automatic derivation:
- Mastered basic and advanced derivation patterns
- Handled dependent types, GADTs, and constraints
- Learned to verify derived generators work correctly

You now have comprehensive understanding of when and how to use `deriveGen` effectively.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Customizing Generator Behavior
- How-to: Integrating Hand-written Generators
- Explanation: How Automatic Derivation Works Internally

Or experiment by creating complex types with multiple constraints and see how DepTyCheck handles them.