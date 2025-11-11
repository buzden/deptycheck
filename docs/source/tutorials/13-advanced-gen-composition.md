# Mastering Complex Generation: Advanced Generator Composition

## What We'll Accomplish
In this tutorial, we'll explore sophisticated generator composition techniques. By the end, you'll:
- Create complex generator pipelines
- Master advanced transformation patterns
- Build generators with sophisticated constraints
- Have expert-level composition skills

## Prerequisites
Before we begin, make sure you have:
- Completed the basic generator tutorials
- Strong understanding of monadic composition
- Idris 2 installed and DepTyCheck available in your project

## Step 1: Build Complex Transformation Pipelines

Let's start by creating sophisticated generator pipelines. Create `AdvancedComposition.idr`:

```idris
module AdvancedComposition

import Data.Fuel
import Test.DepTyCheck.Gen
import Data.List
import Data.String

%default total

-- Complex transformation pipeline
genUserProfile : Gen MaybeEmpty (String, Nat, Bool)
genUserProfile = do
  -- Start with basic generators
  name <- elements ["Alice", "Bob", "Charlie", "Diana"]
  age <- elements [18..65]
  
  -- Conditional generation based on previous values
  isAdmin <- if length name > 4 
             then elements [True, False] 
             else pure False
  
  -- Transform final result
  let formattedName = toUpper name
  pure (formattedName, age, isAdmin)

main : IO ()
main = do
  putStrLn "Testing complex transformation pipeline:"
  let profiles = take 5 $ unGen1 (limit 10) genUserProfile
  traverse_ (putStrLn . show) profiles
```

**Expected result**: You should see formatted user profiles with conditional admin status.

**What to notice**: We're building complex logic into the generator pipeline.

## Step 2: Master Nested Generator Composition

Now let's explore nested composition patterns:

```idris
-- Continue in AdvancedComposition.idr

-- Nested conditional generation
genComplexPermission : Gen MaybeEmpty (String, List String)
genComplexPermission = do
  role <- elements ["admin", "user", "guest", "moderator"]
  
  -- Permission generation depends on role
  permissions <- case role of
    "admin" => elements [["read", "write", "delete", "manage"]]
    "moderator" => elements [["read", "write", "moderate"]]
    "user" => elements [["read", "write"]]
    _ => elements [["read"]]  -- guest
  
  -- Additional constraints
  suchThat (pure (role, permissions)) \(r, perms) => 
    not (null perms) && (r == "admin" ==> "manage" `elem` perms)

genUserSystem : Gen MaybeEmpty ((String, List String), (String, Nat, Bool))
genUserSystem = do
  permission <- genComplexPermission
  profile <- genUserProfile
  
  -- Ensure consistency between permission and profile
  suchThat (pure (permission, profile)) \((role, _), (_, _, isAdmin)) =>
    (role == "admin") == isAdmin

main : IO ()
main = do
  putStrLn "Testing nested composition:"
  let systems = take 5 $ unGen1 (limit 10) genUserSystem
  traverse_ (putStrLn . show) systems
```

**Expected result**: You should see consistent user-permission systems.

**What to notice**: Complex constraints ensure logical consistency across generated data.

## Step 3: Advanced Constraint Handling

Let's explore sophisticated constraint patterns:

```idris
-- Continue in AdvancedComposition.idr

-- Generator with multiple interdependent constraints
genValidTriangle : Gen MaybeEmpty (Nat, Nat, Nat)
genValidTriangle = do
  a <- elements [1..20]
  b <- elements [1..20]
  c <- elements [1..20]
  
  -- Multiple constraints
  suchThat (pure (a, b, c)) \(x, y, z) =>
    let sorted = sort [x, y, z]
        [s1, s2, s3] = sorted
    in s1 + s2 > s3 &&      -- Triangle inequality
       s1 > 0 &&            -- Positive sides
       s3 - s1 < s2         -- Additional constraint

-- Generator that builds on previous attempts
genOptimizedTriangle : Gen MaybeEmpty (Nat, Nat, Nat)
genOptimizedTriangle = 
  -- Try multiple times with increasingly specific ranges
  oneOf
    [ genValidTriangle
    , do
        base <- elements [5..15]
        a <- elements [base..base+10]
        b <- elements [a..a+5]
        c <- elements [b..b+3]
        suchThat (pure (a, b, c)) \(x, y, z) => x + y > z
    ]

main : IO ()
main = do
  putStrLn "Testing advanced constraints:"
  let triangles = take 5 $ unGen1 (limit 10) genOptimizedTriangle
  traverse_ (putStrLn . show) triangles
```

**Expected result**: You should see valid triangles with various characteristics.

**What to notice**: We're using multiple strategies to generate valid data efficiently.

## Step 4: Stateful Generator Patterns

Let's explore stateful generation patterns:

```idris
-- Continue in AdvancedComposition.idr

-- Generator that maintains state across generations
genSequentialIds : Gen NonEmpty (List (Nat, String))
genSequentialIds = do
  -- Start with initial state
  let startId = 1
  names <- elements ["item", "entry", "record", "element"]
  
  -- Generate sequence with state
  go startId (elements [1..5]) names
where
  go : Nat -> Gen NonEmpty Nat -> Gen NonEmpty String -> Gen NonEmpty (List (Nat, String))
  go currentId countGen nameGen = do
    count <- countGen
    if count == 0 
      then pure []
      else do
        name <- nameGen
        let item = (currentId, name)
        rest <- go (currentId + 1) countGen nameGen
        pure (item :: rest)

-- Generator with accumulating constraints
genUniquePairs : Gen MaybeEmpty (List (Nat, Nat))
genUniquePairs = do
  pairs <- elements [1..5] >>= \n => 
    go n [] (elements [1..10]) (elements [1..10])
  suchThat (pure pairs) (\ps => 
    let allNats = concatMap (\(a, b) => [a, b]) ps
    in length (nub allNats) == length allNats  -- All numbers unique
  )
where
  go : Nat -> List (Nat, Nat) -> Gen NonEmpty Nat -> Gen NonEmpty Nat -> Gen NonEmpty (List (Nat, Nat))
  go 0 acc _ _ = pure (reverse acc)
  go n acc genA genB = do
    a <- genA
    b <- genB
    go (n - 1) ((a, b) :: acc) genA genB

main : IO ()
main = do
  putStrLn "Testing stateful patterns:"
  
  putStrLn "Sequential IDs:"
  let sequences = take 3 $ unGen1 (limit 10) genSequentialIds
  traverse_ (putStrLn . show) sequences
  
  putStrLn "\nUnique pairs:"
  let pairs = take 3 $ unGen1 (limit 10) genUniquePairs
  traverse_ (putStrLn . show) pairs
```

**Expected result**: You should see sequential IDs and unique number pairs.

**What to notice**: Stateful patterns allow complex generation with internal consistency.

## Step 5: Advanced Recursive Patterns

Let's explore sophisticated recursive generation:

```idris
-- Continue in AdvancedComposition.idr

data Expr = Lit Nat | Add Expr Expr | Mul Expr Expr

-- Smart recursive generator with depth control
genSmartExpr : Fuel -> Gen MaybeEmpty Expr
genSmartExpr Dry = Lit <$> elements [0..10]
genSmartExpr (More fuel) = frequency
  [ (1, Lit <$> elements [0..10])                          -- 20% leaves
  , (2, do                                                  -- 40% additions
        left <- genSmartExpr fuel
        right <- genSmartExpr fuel
        pure (Add left right)
    )
  , (2, do                                                  -- 40% multiplications
        left <- genSmartExpr fuel
        right <- genSmartExpr fuel
        pure (Mul left right)
    )
  ]

-- Generator that avoids trivial expressions
genNonTrivialExpr : Fuel -> Gen MaybeEmpty Expr
genNonTrivialExpr fuel = suchThat (genSmartExpr fuel) nonTrivial
where
  nonTrivial : Expr -> Bool
  nonTrivial (Lit _) = True
  nonTrivial (Add (Lit x) (Lit y)) = x + y > 0
  nonTrivial (Mul (Lit x) (Lit y)) = x * y > 0
  nonTrivial _ = True

main : IO ()
main = do
  putStrLn "Testing advanced recursive patterns:"
  
  putStrLn "Smart expressions:"
  let exprs = take 5 $ unGen1 (limit 3) (genSmartExpr (limit 3))
  traverse_ (putStrLn . show) exprs
  
  putStrLn "\nNon-trivial expressions:"
  let nontrivial = take 5 $ unGen1 (limit 3) (genNonTrivialExpr (limit 3))
  traverse_ (putStrLn . show) nontrivial
```

**Expected result**: You should see complex expression trees with controlled structure.

**What to notice**: We're using frequency and constraints to control expression complexity.

## What We Accomplished

Congratulations! We've mastered advanced generator composition:
- Built complex transformation pipelines
- Created sophisticated constraint systems
- Implemented stateful generation patterns
- Mastered recursive generation with smart controls

You now have expert-level skills for building sophisticated test data generators.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Performance Optimization for Complex Generators
- How-to: Testing Domain-Specific Business Rules
- Explanation: Generator Performance Characteristics

Or experiment by creating generators for your most complex domain models with intricate business logic.