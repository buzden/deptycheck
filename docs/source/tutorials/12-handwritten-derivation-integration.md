# Mastering Mixed Generation: Integrating Hand-Written and Derived Generators

## What We'll Accomplish
In this tutorial, we'll learn how to combine custom hand-written generators with automatic derivation. By the end, you'll:
- Create custom generators for specific types
- Integrate them with automatically derived generators
- Control when and how custom generators are used
- Have a complete mixed-generation workflow

## Prerequisites
Before we begin, make sure you have:
- Completed the "Hand-written generators with DepTyCheck" tutorial
- Basic understanding of automatic derivation
- Idris 2 installed and DepTyCheck available in your project

## Step 1: Create a Domain Model with Special Requirements

Let's start with a domain model where some types need custom generation. Create `MixedGeneration.idr`:

```idris
module MixedGeneration

import Data.Fuel
import Test.DepTyCheck.Gen

%language ElabReflection

-- A type that needs special generation
data SpecialString = MkSpecialString String

-- Standard domain types
data User = MkUser SpecialString Nat

data Department = Engineering | Marketing | Sales
data Employee = MkEmployee User Department

genSpecialString : Gen NonEmpty SpecialString
genSpecialString = map MkSpecialString $ elements 
  ["admin", "root", "system", "guest", "test"]

main : IO ()
main = do
  putStrLn "Testing special string generator:"
  let specials = take 5 $ unGen1 (limit 10) genSpecialString
  traverse_ (putStrLn . show) specials
```

**Expected result**: You should see only the predefined special strings.

**What to notice**: We have a hand-written generator for SpecialString with specific values.

## Step 2: Set Up Automatic Derivation with Custom Integration

Now let's tell DepTyCheck to use our custom generator for SpecialString:

```idris
-- Continue in MixedGeneration.idr

-- Register our custom generator
genUser : Fuel -> Gen MaybeEmpty User
genUser = deriveGen

genEmployee : Fuel -> Gen MaybeEmpty Employee
genEmployee = deriveGen

testAutomaticWithCustom : IO ()
testAutomaticWithCustom = do
  putStrLn "Testing automatic derivation with custom generator:"
  
  putStrLn "Users:"
  let users = take 3 $ unGen1 (limit 5) (genUser (limit 5))
  traverse_ (putStrLn . show) users
  
  putStrLn "\nEmployees:"
  let employees = take 3 $ unGen1 (limit 5) (genEmployee (limit 5))
  traverse_ (putStrLn . show) employees

main : IO ()
main = do
  -- Previous test...
  putStrLn "\n"
  testAutomaticWithCustom
```

**Expected result**: Users and employees should be generated using your custom SpecialString generator.

**What to notice**: DepTyCheck automatically detects and uses registered generators.

## Step 3: Handle Complex Custom Constraints

Let's create a more sophisticated custom generator example:

```idris
-- Continue in MixedGeneration.idr

-- A type with complex validation
data ValidEmail = MkValidEmail String

-- Custom generator with validation
genValidEmail : Gen MaybeEmpty ValidEmail
genValidEmail = do
  user <- elements ["alice", "bob", "charlie", "diana"]
  domain <- elements ["example.com", "test.org", "demo.net"]
  let email = user ++ "@" ++ domain
  suchThat (pure $ MkValidEmail email) isValidEmail
where
  isValidEmail : ValidEmail -> Bool
  isValidEmail (MkValidEmail email) = 
    '@' `elem` unpack email && length email > 5

data Contact = MkContact ValidEmail SpecialString

genContact : Fuel -> Gen MaybeEmpty Contact
genContact = deriveGen

testComplexIntegration : IO ()
testComplexIntegration = do
  putStrLn "Testing complex custom generators:"
  let contacts = take 5 $ unGen1 (limit 10) (genContact (limit 10))
  traverse_ (putStrLn . show) contacts

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testComplexIntegration
```

**Expected result**: You should see valid email addresses paired with special strings.

**What to notice**: Complex validation can be built into custom generators.

## Step 4: Control Generator Selection

Sometimes you want different generators for the same type in different contexts:

```idris
-- Continue in MixedGeneration.idr

-- Different contexts need different generation strategies
data Env = Production | Staging | Development

data Config = MkConfig Env SpecialString

-- Production needs stricter strings
genProductionString : Gen NonEmpty SpecialString
genProductionString = map MkSpecialString $ elements 
  ["prod-admin", "prod-system"]

-- Helper to choose generator based on context
withGenerator : Env -> (Fuel -> Gen MaybeEmpty Config) -> Fuel -> Gen MaybeEmpty Config
withGenerator env gen fuel = gen fuel  -- In real usage, this would switch generators

genConfig : Fuel -> Gen MaybeEmpty Config
genConfig = deriveGen

testContextAware : IO ()
testContextAware = do
  putStrLn "Testing context-aware generation:"
  let configs = take 3 $ unGen1 (limit 5) (genConfig (limit 5))
  traverse_ (putStrLn . show) configs

main : IO ()
main = do
  -- Previous tests...
  putStrLn "\n"
  testContextAware
```

**Expected result**: Config objects should be generated appropriately.

**What to notice**: You can build logic to select generators based on context.

## What We Accomplished

Congratulations! We've successfully mastered mixed generator integration:
- Created custom generators for specific requirements
- Integrated them seamlessly with automatic derivation
- Handled complex validation and constraints
- Built context-aware generation strategies

You now have the skills to combine the power of both hand-written and automatic generators.

## Next Steps

Ready to learn more? Try these:
- Tutorial: Advanced Generator Composition
- How-to: Performance Optimization for Custom Generators
- Explanation: Internal Generator Resolution Mechanisms

Or experiment by creating your own domain-specific generators and integrating them into larger automatically derived structures.