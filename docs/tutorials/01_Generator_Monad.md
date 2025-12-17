# 1. The Generator Monad: Your First Generator

Welcome to `DepTyCheck`! This tutorial is a hands-on guide that will help you learn the most important skill in property-based testing: generating random test data.

We will keep things practical and focus on what you need to get started. You'll write code, run it, and see the results immediately.

### Our Goal

In this tutorial, we will guide you step by step to create a generator for the following `UserProfile` data type:

```idris
data UserProfile = MkProfile String Nat
```

By the end, you will have a working program that produces random user profiles, like this:

```
MkProfile "Alice" 37 : UserProfile
```

### Prerequisites

This tutorial assumes you have a working Idris 2 installation and have added `deptycheck` as a dependency in your project's `.ipkg` file.

---

## Step 1: Your First Generator

Let's start by creating a generator that always produces the *same* value. This will confirm our setup is working.

1.  **Create a new file** named `Tutorial.idr`.

2.  **Add the following code** to it. We'll define our data type and import the necessary `DepTyCheck` modules.

    ```idris
    module Tutorial

    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Runner

    data UserProfile = MkProfile String Nat

    -- A generator that always produces the same, constant user profile
    genConstantUser : Gen1 UserProfile
    genConstantUser = pure (MkProfile "Alice" 30)
    ```
    The `pure` function creates the simplest possible "recipe": one that always returns the exact value you give it. The type `Gen1` means this generator is guaranteed to produce a value.

3.  **Run your generator.** Open a REPL and load your file. Then, use the `pick1` function to get a single value from your generator:

    ```idris
    :exec pick1 genConstantUser
    ```

    You will see the following output, every single time:

    ```
    MkProfile "Alice" 30 : UserProfile
    ```

You've just created and run your first generator! Now, let's make it more interesting by adding some randomness.

---

## Step 2: Adding Randomness

Instead of a fixed age, let's generate a random one. We'll use the `choose` function for this.

1.  **Modify your file** to create a new generator.

    ```idris
    -- A generator for a user with a random age between 18 and 99
    genRandomAgeUser : Gen1 UserProfile
    genRandomAgeUser = MkProfile "Alice" <$> choose (18, 99)
    ```
    Here's what's new:
    *   `choose (18, 99)` creates a recipe for picking a random number in that range.
    *   The `<$>` operator takes the result from the recipe on the right (our random number) and feeds it into the function on the left (`MkProfile "Alice"`).

2.  **Run it multiple times** in the REPL:

    ```idris
    :exec pick1 genRandomAgeUser
    :exec pick1 genRandomAgeUser
    ```

    This time, you'll see a different result with each run:

    ```
    MkProfile "Alice" 81 : UserProfile
    MkProfile "Alice" 25 : UserProfile
    ```

Success! You've introduced randomness into your data.

---

## Step 3: Combining Two Random Generators

Now, let's make the name random too. We need to combine two different random recipes.

1.  **Add a new generator** that combines a random name and a random age.

    ```idris
    -- A generator for a user with a random name and a random age
    genUserProfile : Gen1 UserProfile
    genUserProfile = MkProfile <$> elements ["Alice", "Bob", "Charlie"] <*> choose (18, 99)
    ```
    Here's the change:
    *   `elements ["Alice", "Bob", "Charlie"]` creates a recipe for picking a random name from a list.
    *   The `<*>` operator is the key: it lets us combine two recipes. It runs the name recipe and the age recipe, then feeds *both* results into `MkProfile`.

2.  **Run your new generator** a few times:

    ```idris
    :exec pick1 genUserProfile
    :exec pick1 genUserProfile
    ```

    You'll now see completely random user profiles!

    ```
    MkProfile "Charlie" 65 : UserProfile
    MkProfile "Alice" 22 : UserProfile
    ```

---

## Step 4: Choosing Between Generators

What if you want to generate more varied data? For example, maybe you want to generate a user who is either an "Admin" or a "Guest", with "Guest" being more common.

`DepTyCheck` provides `oneOf` for equal choices and `frequency` for weighted choices.

1.  **Add these new generators** to your file.

    ```idris
    -- A generator for a user role, with each role having an equal chance
    genRole : Gen1 String
    genRole = oneOf [pure "Admin", pure "User", pure "Guest"]

    -- A generator for a user type, where "Standard" is 4x more likely than "Premium"
    genUserType : Gen1 String
    genUserType = frequency [ (4, pure "Standard"), (1, pure "Premium") ]
    ```
    *   `oneOf` takes a list of generators and chooses one of them with equal probability.
    *   `frequency` takes a list of `(weight, generator)` pairs. The weights determine the probability. Here, there are 5 total "parts" (4+1), so "Standard" has a 4/5 chance and "Premium" has a 1/5 chance.

2.  **Run them in the REPL.**

    ```idris
    :exec pick1 genRole
    :exec pick1 genUserType
    ```
    If you run `:exec pick1 genUserType` many times, you will notice that `"Standard"` appears much more often than `"Premium"`.

---

## Step 5: Dependent Generation

So far, the random values we've generated (name, age) have been independent of each other. But what if the **type** of one value needs to depend on the *value* of another?

This is the core challenge of generating dependent types. For example, let's generate a pair containing a random length `n` and a `Vect` that has exactly `n` elements. The type `Vect n Bool` depends directly on the value `n`.

This is called **dependent generation**. We must first generate `n`, and *then* use that value to create a generator for a vector of that specific type. We use `do` notation for this.

1.  **Add this generator** to `Tutorial.idr`. It will create a dependent pair `(n ** Vect n Bool)`.

    ```idris
    import Data.Vect

    -- A generator for a dependent pair: a random length `n` and a vector of that length
    genDependentVect : Gen1 (n ** Vect n Bool)
    genDependentVect = do
      n   <- choose (1, 5) -- Step 1: Generate a random length `n`
      vec <- vectOf n (elements [True, False]) -- Step 2: Generate a vector of that *exact* length
      pure (n ** vec) -- Step 3: Package them into a dependent pair with (**)
    ```

    This `do` block is a sequence of dependent instructions:

    1.  `n <- choose (1, 5)`: A random `Nat` is generated. Let's say the result is `3`.
    2.  `vec <- vectOf n ...`: *Because* `n` has the value `3`, this line creates and runs a generator for the type `Vect 3 Bool`.
    3.  `pure (n ** vec)`: The value `3` and the generated vector (e.g., `[True, False, True]`) are bundled into a dependent pair using the `**` constructor.

2.  **Run it in the REPL.**

    ```idris
    :exec pick1 genDependentVect
    (3 ** [True, True, False]) : (n : Nat ** Vect n Bool)

    :exec pick1 genDependentVect
    (5 ** [False, True, False, True, True]) : (n : Nat ** Vect n Bool)
    ```
    Notice that the length of the vector in the output always matches the number next to it. This powerful technique is what allows `DepTyCheck` to generate valid data for complex, dependent types.

---
## Step 6: Generating a Collection

Finally, let's generate a list of test users. You can use the `listOf` combinator to run your generator multiple times and collect the results.

1.  **Add one last generator** to your `Tutorial.idr` file.

    ```idris
    -- A generator that produces a list of 5 random user profiles
    genFiveUsers : Gen1 (List UserProfile)
    genFiveUsers = listOf 5 genUserProfile
    ```
    The `listOf` function takes a number `n` and a generator, and creates a new recipe that runs the generator `n` times.

2.  **Run it in the REPL:**

    ```idris
    :exec pick1 genFiveUsers
    ```
    The output will be a list of five unique, randomly-generated users:

    ```
    [MkProfile "Bob" 45, MkProfile "Bob" 88, MkProfile "Alice" 19, MkProfile "Charlie" 80, MkProfile "Bob" 52] : List UserProfile
    ```

---

## Congratulations!

You've learned the fundamentals of creating test data generators with `DepTyCheck`.

You now know how to:
*   ✅ Create a simple, constant generator with `pure`.
*   ✅ Generate random numbers and pick from lists with `choose` and `elements`.
*   ✅ Combine simple recipes into complex ones using `<$>` and `<*>`.
*   ✅ Create weighted and unweighted choices with `frequency` and `oneOf`.
*   ✅ Create dependent values using `do` notation.
*   ✅ Generate a collection of random data with `listOf`.
*   ✅ Run any generator to see the result using `pick1`.

This pattern of building small, simple recipes and combining them into larger ones is the core of `DepTyCheck`.

### Next Steps

You've mastered the basics. Where you go next depends on your needs:

*   Ready to have `DepTyCheck` do the work for you? Continue to our next tutorial to learn about **[Automatic Generator Derivation with `deriveGen`](./04-automatic-generator-derivation.md)**.
