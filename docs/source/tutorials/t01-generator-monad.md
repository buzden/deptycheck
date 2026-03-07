# 1. The Generator Monad: Your First Generator

Welcome to `DepTyCheck`! This tutorial is a hands-on guide that will help you learn the most important skill in property-based testing: generating random test data.

We will keep things practical and focus on what you need to get started. You'll write code, run it, and see the results immediately.

## Our Goal

In this tutorial, we will guide you step by step to create a generator for the following `UserProfile` data type:

    ```idris
    data UserProfile = MkProfile String Nat
    ```

By the end, you will have a working program that produces random user profiles, like this:

    ```idris
    MkProfile "Alice" 37 : UserProfile
    ```

## Prerequisites

This tutorial assumes you have completed [Installation and First Steps](t00-installation-and-setup.md) and have a working Idris 2 installation with DepTyCheck configured for your `tutorial.ipkg`.

---

## Step 1: Your First Generator

Let's start by creating a generator that always produces the _same_ value. This will confirm our setup is working.

### Create a new file named `Tutorial.idr`.

```idris
import Test.DepTyCheck.Gen
import Data.Vect

%language ElabReflection
```

### Add the following code to it. We'll define our data type and import the necessary `DepTyCheck` modules.

```idris
data UserProfile = MkProfile String Nat

Show UserProfile where
  show (MkProfile s y) = "MkProfile " ++ show s ++ " " ++ show y

-- A generator that always produces the same, constant user profile
genConstantUser : Gen1 UserProfile
genConstantUser = pure (MkProfile "Alice" 30)
```

> [!NOTE]\
> The `pure` function creates the simplest possible "recipe": one that always returns the exact value you give it. The type `Gen1` means this generator is guaranteed to produce a value.

### Run your generator.

To test your first generator lets do the following:

```bash
echo -e ':exec printLn =<< pick1 genConstantUser' |
    rlwrap pack --extra-args="--no-banner" repl ./Tutorial.idr
```

Here we do:

| | |
| --- | ---------- |
| `echo -e` and `\|` | We are going to run Idris2 in REPL mode, pass the input, wait for the output and close |
| `:exec` | It is actually the Idris2 REPL command to run something in `IO` monad. For `:exec ?wat` the `?wat` is `IO _`. |
| `printLn =<<` | To run the generator and force `show` some output of the result. `:exec:` itself only runs something in `IO` but drops any result, so `:exec pure "something"` would not show you anything. |
| `pick1 genConstantUser` | *We are very close, that's what is needed.* |
| `rlwrap` | To be honest for the single run it is not needed but we let it be there for a remind that Idris2 REPL lacks its support out of the box |
| `pack` | DepTyCheck depends on a set of libraries, so, `pack` launches `idris2` with the full set of required things |
| `--extra-args="--no-banner"` | Just a little look & feel improvement to reduce the size of REPL output for every turn. `--extra-args` passes following string as options to `idris2` where `--no-banner` disables Idris2 welcome banner to show. |
| `repl` | It actually instructs `pack` to run `idris2` in REPL mode
| `./Tutorial.idr` |


You will see an output, similar to the following:

```text
MkProfile "Alice" 30
```

You've just created and run your first generator! Now, let's make it more interesting by adding some randomness.

---

## Step 2: Adding Randomness

Instead of a fixed age, let's generate a random one. We'll use the `choose` function for this.

### Modify your file to create a new generator.

```idris
-- A generator for a user with a random age between 18 and 99
genRandomAgeUser : Gen1 UserProfile
genRandomAgeUser = MkProfile "Alice" <$> choose (18, 99)
```

Here's what's new:
-   `choose (18, 99)` creates a recipe for picking a random number in that range.

> [!NOTE]\
> The `choose` function randomly picks between two generators with equal probability (50/50). This gives you a simple way to add variation to your generators.
-   The `<$>` operator takes the result from the recipe on the right (our random number) and feeds it into the function on the left (`MkProfile "Alice"`).

### Run it multiple times

```bash
echo -e ':exec printLn =<< pick1 genRandomAgeUser' |
    rlwrap pack --extra-args="--no-banner" repl ./Tutorial.idr
```

```bash
echo -e ':exec printLn =<< pick1 genRandomAgeUser' |
    rlwrap pack --extra-args="--no-banner" repl ./Tutorial.idr
```

This time, you'll see a different result with each run:

```text
MkProfile "Alice" 22
MkProfile "Alice" 35
```

Success! You've introduced randomness into your data.

---

## Step 3: Combining Two Random Generators

Now, let's make the name random too. We need to combine two different random recipes.

### Add a new generator that combines a random name and a random age.

```idris
-- A generator for a user with a random name and a random age
genUserProfile : Gen1 UserProfile
genUserProfile = MkProfile <$> elements ["Alice", "Bob", "Charlie"] <*> choose (18, 99)
```

    Here's the change:
    *   `elements ["Alice", "Bob", "Charlie"]` creates a recipe for picking a random name from a list.
    *   The `<*>` operator is the key: it lets us combine two recipes. It runs the name recipe and the age recipe, then feeds _both_ results into `MkProfile`.

### Run your new generator a few times:

```bash
echo -e ':exec printLn =<< pick1 genUserProfile' |
    rlwrap pack --extra-args="--no-banner" repl ./Tutorial.idr
```

```bash
echo -e ':exec printLn =<< pick1 genUserProfile' |
    rlwrap pack --extra-args="--no-banner" repl ./Tutorial.idr
```

You'll now see completely random user profiles!

```text
MkProfile "Alice" 33
MkProfile "Bob" 47
```

---

## Step 4: Choosing Between Generators

What if you want to generate more varied data? For example, maybe you want to generate a user who is either an "Admin" or a "Guest", with "Guest" being more common.

`DepTyCheck` provides `oneOf` for equal choices and `frequency` for weighted choices.

### Add these new generators to your file.

```idris
-- A generator for a user role, with each role having an equal chance
genRole : Gen1 String
genRole = oneOf [pure "Admin", pure "User", pure "Guest"]

-- A generator for a user type, where "Standard" is 4x more likely than "Premium"
genUserType : Gen1 String
genUserType = frequency [ (4, pure "Standard"), (1, pure "Premium") ]
```


-   `oneOf` takes a list of generators and chooses one of them with equal probability.
-   `frequency` takes a list of `(weight, generator)` pairs. The weights determine the probability. Here, there are 5 total "parts" (4+1), so "Standard" has a 4/5 chance and "Premium" has a 1/5 chance.

### Run them in the REPL.

```bash
echo -e ':exec printLn =<< pick1 genRole' |
    rlwrap pack --extra-args="--no-banner" repl ./Tutorial.idr
```

```bash
echo -e ':exec printLn =<< pick1 genUserType' |
    rlwrap pack --extra-args="--no-banner" repl ./Tutorial.idr
```

Sample output:

```text
"Guest"
"Standard"
```

If you run `pick1 genUserType` many times, you will notice that `"Standard"` appears much more often than `"Premium"`.

---

## Step 5: Dependent Generation

So far, the random values we've generated (name, age) have been independent of each other. But what if the __type__ of one value needs to depend on the _value_ of another?

This is the core challenge of generating dependent types. For example, let's generate a pair containing a random length `n` and a `Vect` that has exactly `n` elements. The type `Vect n Bool` depends directly on the value `n`.

This is called **dependent generation**. We must first generate `n`, and _then_ use that value to create a generator for a vector of that specific type. We use `do` notation for this.

### Add this generator to `Tutorial.idr`. It will create a dependent pair `(n ** Vect n Bool)`.

```idris
-- A generator for a dependent pair: a random length `n` and a vector of that length
genDependentVect : Gen1 (n ** Vect n Bool)
genDependentVect = do
    n   <- choose (1, 5) -- Step 1: Generate a random length `n`
    vec <- vectOf {n} (elements [True, False]) -- Step 2: Generate a vector of that exact length
    pure (n ** vec) -- Step 3: Package them into a dependent pair with (**)
```

This `do` block is a sequence of dependent instructions:

1.  `n <- choose (1, 5)`: A random `Nat` is generated. Let's say the result is `3`.
2.  `vec <- vectOf {n} ...`: _Because_ `n` has the value `3`, this line creates and runs a generator for the type `Vect 3 Bool`. We have to pass it as a named argument because it is used at the type definition of `vectOf`.
3.  `pure (n ** vec)`: The value `3` and the generated vector (e.g., `[True, False, True]`) are bundled into a dependent pair using the `**` constructor.

### Run it in the REPL.

```bash
echo -e ':exec printLn =<< pick1 genDependentVect' |
    rlwrap pack --extra-args="--no-banner" repl ./Tutorial.idr
```

For multiple times the output might be:

```text
(3 ** [False, False, False])
(5 ** [True, True, True, True, True])
(2 ** [True, False])
```

Notice that the length of the vector in the output always matches the number next to it. This powerful technique is what allows `DepTyCheck` to generate valid data for complex, dependent types.

---
## Step 6: Generating a Collection

Finally, let's generate a list of test users. You can use the `listOf` combinator to run your generator multiple times and collect the results.

### Add one last generator to your `Tutorial.idr` file.

```idris
-- A generator that produces a list of 5 random user profiles
genFiveUsers : Gen1 (List UserProfile)
genFiveUsers = listOf {length=pure 5} genUserProfile
```

The `listOf` function takes a `length` generator (which we provide as a constant `5`), and creates a new recipe that runs the generator how a provided `length` generator  generated times.

### Run it in the REPL:

```bash
echo -e ':exec printLn =<< pick1 genFiveUsers' |
    rlwrap pack --extra-args="--no-banner" repl ./Tutorial.idr
```

The output will be a list of five unique, randomly-generated users:

```text
[MkProfile "Alice" 84, MkProfile "Charlie" 30, MkProfile "Bob" 41, MkProfile "Bob" 59, MkProfile "Bob" 67]
```

---

## Next Steps

You've mastered the basics. Where you go next depends on your needs:

-   **Want to handle types that might be empty?** Continue to [Handling Emptiness](t02-handling-emptiness.md) to learn about `Gen0`, `empty`, and `pick`.
-   **Ready to have `DepTyCheck` do the work for you?** Continue to [Automatic Generator Derivation](t04-automatic-generator-derivation.md) to learn about `deriveGen`.
