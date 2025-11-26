# 5. Automatic Derivation: Instructing `deriveGen`

In the previous tutorials, we treated `deriveGen` as a simple, one-shot macro. But for a GADT (Generalized Algebraic Data Type) like `Vect`, which is indexed by a value, a simple `deriveGen` call isn't enough. How do we tell it *what kind* of `Vect` we want?

The answer is the function signature. The signature is not just a type; it is a blueprint of your intent that tells `deriveGen` exactly what to do.

### Our Goal

In this tutorial, we will learn to command `deriveGen` by writing three different function signatures for the `Vect` type. By the end of this tutorial, you will have built:

1.  A generator for a `Vect` of a **specific, given** length.
2.  A generator that produces a `Vect` of a **random, generated** length.
3.  A flexible generator that takes both a **given** length and an **external generator** for its elements.

This will give you a deep understanding of how to use signatures to control `deriveGen`.

### Prerequisites

-   All previous tutorials, especially [Measuring Your Test Coverage](03-measuring-test-coverage.md).

---

## Step 1: The Setup

First, let's create our file and add the necessary imports. We will be using `Vect` throughout this tutorial.

1.  **Create a new file** named `DeriveTutorial.idr`.

2.  **Add the following boilerplate.** This includes the `ElabReflection` pragma and all the modules we will need.

    ```idris
    %language ElabReflection

    module DeriveTutorial

    import Deriving.DepTyCheck.Gen
    import Data.Vect
    import Data.Fuel

    import Test.DepTyCheck.Gen
    import Test.DepTyCheck.Runner
    import System.Random.Pure.StdGen
    ```

---

_Note: For the following steps, you can put all the code in the same `DeriveTutorial.idr` file and temporarily rename the `main` function you want to run as `main` before compiling._

## Step 2: Scenario A - Generating a `Vect` of a Given Length

Our first goal is to create a generator that produces a `Vect` of a specific length that we provide as an argument. To do this, we simply place the argument *before* the `Fuel` parameter in the signature.

1.  **Define the generator.** The signature `(n : Nat) -> Fuel -> Gen MaybeEmpty (Vect n String)` tells `deriveGen`: "You will be *given* a `Nat` named `n`. Your job is to produce a `Vect` of that exact length."

    ```idris
    genVectOfLen : (n : Nat) -> Fuel -> Gen MaybeEmpty (Vect n String)
    genVectOfLen = deriveGen
    ```

2.  **Test it.** Let's write a `main` function to call our generator, providing `5` as the length.

    ```idris
    main_A : IO ()
    main_A = do
      putStrLn "--- Generating a Vect of a given length (5) ---"
      Just v <- pick1 (genVectOfLen 5 (limit 10))
        | Nothing => printLn "Generation failed"
      printLn v
      printLn $ "The length is: " ++ show (length v)
    ```

3.  **Compile and run.** The output will show a `Vect` that always has exactly 5 elements, filled with random strings from the default `String` generator.

    ```
    --- Generating a Vect of a given length (5) ---
    ["a", "b", "c", "d", "e"]
    The length is: 5
    ```

By placing `n` before `Fuel`, you have successfully commanded `deriveGen` to use it as a fixed input.

---

## Step 3: Scenario B - Generating a `Vect` of a Random Length

What if we don't want to provide a specific length? What if we want the generator itself to invent a random length? To do this, we use a **dependent pair** in the return type.

1.  **Define the generator.** The signature `Fuel -> Gen MaybeEmpty (n ** Vect n String)` tells `deriveGen`: "Your job is to first generate a random `Nat` (which you will call `n`), and then generate a `Vect` of that length. When you are done, give me back both `n` and the `Vect`."

    ```idris
    genRandomVect : Fuel -> Gen MaybeEmpty (n ** Vect n String)
    genRandomVect = deriveGen
    ```

2.  **Test It.** This time, when we call the generator, we don't provide a length. The generator will produce a pair containing the length it chose and the vector it created.

    ```idris
    main_B : IO ()
    main_B = do
      putStrLn "--- Generating a Vect of a random length ---"
      replicate 3 $ do
        Just (n ** v) <- pick1 (genRandomVect (limit 10))
          | Nothing => printLn "Generation failed"
        printLn $ "Got a Vect of length " ++ show n ++ ": " ++ show v
    ```

3.  **Compile and run.** You will see vectors of different, random lengths each time you run it.

    ```
    --- Generating a Vect of a random length ---
    Got a Vect of length 3: ["a", "b", "c"]
    Got a Vect of length 0: []
    Got a Vect of length 5: ["d", "e", "f", "g", "h"]
    ```

By moving the parameter `n` from an input to a **generated** part of the output using the `**` syntax, you have completely changed `deriveGen`'s behavior.

---

## Step 4: The Flexible Generator - Combining Patterns

Let's combine the patterns we've learned. Our final generator will be the most flexible: it will take a `Nat` as a *given* input, but it will also take an *external generator* hint for the element type using the `=>` syntax.

1.  **Define the generator.** The signature `(n : Nat) -> (Fuel -> Gen MaybeEmpty a) => Fuel -> Gen MaybeEmpty (Vect n a)` tells `deriveGen`: "You will be *given* `n` and a generator for the elements of type `a`. Your job is to use them to produce a `Vect` of the correct length and type."

    ```idris
    genFlexiVect : (n : Nat) -> (Fuel -> Gen MaybeEmpty a) => Fuel -> Gen MaybeEmpty (Vect n a)
    genFlexiVect = deriveGen
    ```

2.  **Test It.** To call this generator, we must provide both the length `n` and an element generator via the `@` syntax.

    ```idris
    main_C : IO ()
    main_C = do
      putStrLn "--- Generating a Vect of length 7 with custom Nat elements ---"
      let myNatGen = choose (100, 200) -- Our custom generator for the elements

      Just v <- pick1 (genFlexiVect 7 @{myNatGen} (limit 10))
        | Nothing => printLn "Generation failed"
      printLn v
    ```

3.  **Compile, run, and observe.** You will see a `Vect` of length 7, filled with numbers between 100 and 200, proving that `deriveGen` correctly used both your given length and your external generator.

    ```
    --- Generating a Vect of length 7 with custom Nat elements ---
    [158, 112, 199, 101, 134, 186, 177]
    ```

---

## Step 5: Generating Proof-Carrying Data

Now for something even more powerful. Let's define a list that is *always* sorted, by construction. The list's definition will carry a proof of its own sortedness.

```idris
data SortedList : Type where
  SNil : SortedList
  SCons : (x : Nat) -> (xs : SortedList) -> {auto prf : isSorted (x :: toList xs)} -> SortedList
where
  toList : SortedList -> List Nat
  toList SNil = []
  toList (SCons x xs) = x :: toList xs

  isSorted : List Nat -> Bool
  isSorted [] = True
  isSorted [_] = True
  isSorted (x :: y :: xs) = x <= y && isSorted (y :: xs)

-- A generator for it
genSortedList : Fuel -> Gen MaybeEmpty SortedList
genSortedList = deriveGen
```

The `SCons` constructor requires a proof that adding the new element `x` to the front of the existing sorted list `xs` will result in a list that is still sorted. How can `deriveGen` possibly find a valid `x`?

**Test it in the REPL.**

```idris
:exec toList <$> pick1 (genSortedList (limit 20))
-- [0, 3, 5, 12, 42] : List Nat

:exec toList <$> pick1 (genSortedList (limit 20))
-- [8, 8, 9, 15, 21, 33] : List Nat
```

`deriveGen` is smart enough to solve the constraints. It understands that to satisfy `{auto prf : isSorted (x :: toList xs)}`, it cannot just pick any random `Nat` for `x`. It must generate an `x` that is less than or equal to the head of `xs`. It does this automatically.

---

## Congratulations!

You have learned to 'speak' to `deriveGen` through its most powerful interface: the type signature. You are no longer just asking it to generate a type; you are giving it a precise blueprint of your intent.

By crafting the signature, you can control what `deriveGen` does:

*   ✅ **Given Parameters (`(n : Nat) -> ...`):** Arguments before `Fuel` are treated as fixed runtime inputs.
*   ✅ **Generated Parameters (`... -> Gen (n ** Vect n a)`):** Using `**` in the return type tells `deriveGen` to invent a value for that parameter for you.
*   ✅ **External Generator Hints (`(...) => ...`):** A constraint tells `deriveGen` to use a generator you provide for a specific type.

Mastering these three patterns gives you the power to create flexible, reusable, and precise automatic generators for even the most complex GADTs.

### Next Steps

Now that you know how to automatically generate data by crafting signatures, you are ready for advanced topics.

*   **How do I fix a biased generator or control generation order?** The default derivation strategy is smart, but sometimes needs more specific guidance. Continue to **[Beyond Fuel: A Tutorial on Structural Recursion](06-beyond-fuel.md)** to learn how to use `instance` declarations to control constructor probabilities and argument generation order.
