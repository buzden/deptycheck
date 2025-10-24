# Chapter 1: Test Value Generator (`Gen`)

Welcome to your first step into `DepTyCheck`! We're thrilled to have you here. This library is all about making it easier to test your code, especially when you're working with Idris's powerful dependent types.

So, let's start with a simple question: how do you test a function? Usually, you call it with some input and check if the output is what you expect.

```idris
-- A function that tells us if a number is even
isEven : Nat -> Bool
isEven n = (n `mod` 2) == 0

-- A simple test
testIsEven : isEven 4 === True
testIsEven = Refl
```

This is great for one value, but what about others? 2? 10? 99? Testing every possible number is impossible. This is where *property-based testing* comes in. Instead of testing individual values, we state a property that should hold true for *all* values, and then we let the computer generate hundreds of random examples to check that property.

To do this, we first need a way to generate all that random test data. That's the problem this chapter's hero, the **`Gen`** type, is here to solve.

## What is a `Gen`?

Think of `Gen a` as a **recipe for creating random values of type `a`**.

A simple recipe might be "pick a random color from a list." In `DepTyCheck`, that looks like this:

```idris
import Test.DepTyCheck.Gen

-- A recipe for generating a random String
genSomeColors : Gen1 String
genSomeColors = elements ["Red", "Green", "Blue"]
```

Let's break that down:
*   `Gen1 String`: This is the type. It reads as "A generator (`Gen`) that is non-empty (`1` is a shorthand for `NonEmpty`) and produces `String`s." We'll talk more about `NonEmpty` soon!
*   `elements [...]`: This is one of the simplest recipe-makers. It says, "randomly and uniformly pick one value from this list."

To actually "cook" the recipe and get a value, we can use a function like `pick1`:

```idris
-- In the Idris REPL:
-- > :exec pick1 genSomeColors
-- Maybe "Green" : Maybe String

-- > :exec pick1 genSomeColors
-- Maybe "Red" : Maybe String
```
As you can see, every time you run it, you might get a different color. You've just created and used your first generator!

## Combining Recipes

Now, what if we need to generate something more complex, like a user profile?

```idris
data User = MkUser String Nat

-- A recipe for a user's name
genName : Gen1 String
genName = elements ["Alice", "Bob", "Charlie"]

-- A recipe for a user's age
genAge : Gen1 Nat
genAge = choose (18, 65) -- pick a random Nat between 18 and 65
```

We have two simple recipes (`genName` and `genAge`) and we want to combine them into a single, more complex recipe to create a `User`. `DepTyCheck` makes this easy with special `[| ... |]` syntax.

```idris
genUser : Gen1 User
genUser = [| MkUser genName genAge |]
```

This code says: "To make a `User`, use the `MkUser` constructor. For the first field (the name), follow the `genName` recipe. For the second field (the age), follow the `genAge` recipe."

It's like plugging smaller recipes into a bigger one.

## Recipes with Choices: `oneOf`

Sometimes, a recipe can offer a choice. Imagine a recipe that says, "For dessert, you can either have cake *or* ice cream." The `oneOf` function does exactly that. It lets you build a new generator by choosing one from a list of existing generators.

```idris
genFruit : Gen1 String
genFruit = elements ["Apple", "Banana"]

genVegetable : Gen1 String
genVegetable = elements ["Carrot", "Broccoli"]

-- A recipe that generates either a fruit or a vegetable
genFood : Gen1 String
genFood = oneOf [genFruit, genVegetable]
```

When you run `genFood`, `DepTyCheck` will first flip a coin. If it's heads, it will use the `genFruit` generator. If it's tails, it will use the `genVegetable` generator. All generators inside `oneOf` have an equal chance of being picked.

## The Secret Ingredient: Dependent Recipes

This is where `DepTyCheck` truly shines, especially with dependent types. What if one part of our recipe depends on a value created in an earlier step?

**Analogy:** Imagine a recipe that says:
1.  *First*, roll a die to get a number `n` from 1 to 6.
2.  *Then*, take exactly `n` scoops of ice cream to make a sundae.

The number of scoops depends on the outcome of the die roll.

In Idris, a classic example is the `Fin n` type, which represents a number from `0` to `n-1`. The value of type `Fin n` *depends* on the number `n`. How could we write a recipe that generates *both* a random number `n` and a valid `Fin n`?

We can use `do`-notation, which lets us chain recipe steps together.

```idris
import Data.Fin

-- First, a helper recipe that for a given `n`, generates a `Fin n`.
-- Don't worry about the details here for now.
genFin : (n : Nat) -> Gen MaybeEmpty (Fin n)
genFin Z     = empty
genFin (S k) = elements' (allFins k)

-- Now, our dependent recipe!
genAnyFin : Gen MaybeEmpty (n ** Fin n)
genAnyFin = do
  -- Step 1: Generate a random number `n` between 1 and 5.
  n <- choose (1, 5)
  -- Step 2: Use `n` to generate a `Fin n`.
  f <- genFin n
  -- Finally, return the pair.
  pure (n ** f)
```

This is incredibly powerful! The `genAnyFin` recipe first follows the `choose (1, 5)` recipe to produce a number `n`. This `n` is then used as an input to the `genFin` recipe-maker, which creates a brand new recipe tailored just for that `n`.

This ability to have later steps depend on the random results of earlier steps is what makes `Gen` a **monad**, and it's essential for testing dependent types.

### A Quick Note on Emptiness

You might have noticed `Gen MaybeEmpty` in the example above. What's that about?

Some types have no values. The most famous is `Fin 0`. It's impossible to create a value of type `Fin 0`. So, what should a recipe for `Fin 0` do? It can't produce a value.

`DepTyCheck` handles this with an "emptiness" tag in the `Gen` type:
*   `Gen NonEmpty a` (or `Gen1 a`): A recipe that is **guaranteed** to produce a value. `genSomeColors` is one of these.
*   `Gen MaybeEmpty a` (or `Gen0 a`): A recipe that **might not** produce a value.

Our `genFin` function cleverly returns an `empty` generator for `genFin 0`, acknowledging that no value can be made. Because it might be empty for some inputs, its return type must be `Gen MaybeEmpty`.

## Under the Hood: The `Gen` Data Structure

So how does this all work? The `Gen` type is not a function that does something; it's a passive **data structure** that describes the steps of the recipe.

Here is a simplified view of its definition:

```idris
data Gen : Emptiness -> Type -> Type where
  -- A recipe for a fixed value.
  Pure  : a -> Gen em a

  -- A recipe for a value from a list.
  -- (Simplified from the real `elements` which uses `OneOf`)
  Elements : List a -> Gen NonEmpty a

  -- A recipe with dependent steps.
  Bind  : Gen em a -> (a -> Gen em b) -> Gen em b

  -- A recipe for choosing between other recipes.
  OneOf : List (Gen NonEmpty a) -> Gen NonEmpty a

  -- A recipe that can't produce a value.
  Empty : Gen MaybeEmpty a
```

When you write `genUser = [| MkUser genName genAge |]`, Idris translates it into a `Bind` structure. When you use `oneOf`, it creates a `OneOf` data value. You are building up a tree-like structure that represents the entire plan.

A function like `pick1` is the "chef" that reads your recipe (`Gen a`) and executes the plan.

```mermaid
sequenceDiagram
    participant U as You
    participant P as pick1
    participant R as Randomness
    participant G as genAnyFin

    U->>P: :exec pick1 genAnyFin
    P->>R: Get a random seed
    P->>G: Follow the recipe with seed
    Note over G: genAnyFin is `do { n <- choose(1,5); ... }`
    G->>R: Use seed to pick n=3
    G-->>G: Now `n` is 3. Next step is `genFin 3`.
    Note over G: genFin 3 is `elements' [0, 1, 2]`
    G->>R: Use new seed to pick from [0, 1, 2]. Let's say `f=1`.
    G-->>P: Result is (3 ** FZ)
    P-->>U: Maybe (3 ** f=1)
```

This diagram shows how the `pick1` function walks through the `Gen` data structure, using a source of randomness at each step to make choices and generate the final value.

## Conclusion

Congratulations! You've just learned the single most important concept in `DepTyCheck`.

You now know that a **`Gen`** is a recipe for making random data. You've seen how to:
*   Create simple recipes from lists (`elements`) and ranges (`choose`).
*   Combine recipes to build values for complex types (`[| ... |]`).
*   Offer choices between different recipes (`oneOf`).
*   Create powerful, dependent recipes where one step depends on the result of a previous one (`do`-notation).

Writing these recipes by hand is a great start, but for large, complex data types, it can become a lot of work. What if `DepTyCheck` could just look at your `data` definition and write the generator for you, automatically?

That's exactly what we'll explore in the next chapter on [Automatic Generator Derivation (`deriveGen`)](02_automatic_generator_derivation___derivegen___.md).

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)