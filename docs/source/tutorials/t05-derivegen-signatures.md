# 5. DeriveGen Signatures: Controlling What Gets Generated

In the previous tutorial, we saw how `deriveGen` can automatically create generators. But how do we tell it _what kind_ of data we want? For example,
should the length of a `Vect` be given as an argument, or should it be randomly generated?

The answer is the function signature. The signature is not just a type; it is a blueprint of your intent that tells `deriveGen` exactly what to do.

## Our Goal

In this tutorial, we will learn to command `deriveGen` by writing three different function signatures for the `Vect` type. By the end of this tutorial,
you will have built:

1. A generator for a `Vect` of a **specific, given** length.
2. A generator that produces a `Vect` of a **random, generated** length.
3. A flexible generator that takes both a **given** length and an **external generator** for its elements.

This will give you a deep understanding of how to use signatures to control `deriveGen`.

## Prerequisites

- All previous tutorials, especially [Measuring Your Test Coverage](t03-measuring-test-coverage.md).

---

## Step 1: The Setup

First, let's create our file and add the necessary imports. We will be using `Vect` throughout this tutorial.

### Create a new file named `DeriveTutorial.idr`

### Add the following boilerplate

This includes the `ElabReflection` pragma and all the modules we will need.

```idris
import Deriving.DepTyCheck.Gen
import Data.Vect
import Data.Fuel

import Test.DepTyCheck.Gen
import System.Random.Pure.StdGen

%language ElabReflection

%hint
genStr : Fuel -> Gen MaybeEmpty String
genStr _ = elements ["a", "b", "c", "d", "f", "g", "h"]

public export
data VectString : (len : Nat) -> Type where
  Nil  : VectString Z
  (::) : (x : String) -> (xs : VectString len) -> VectString (S len)

Show (VectString n) where
  show xs = "[" ++ show' xs ++ "]" where
    show' : forall n . VectString n -> String
    show' Nil        = ""
    show' (x :: Nil) = show x
    show' (x :: xs)  = show x ++ ", " ++ show' xs
```

---

_Note: For the following steps, you can put all the code in the same `DeriveTutorial.idr` file and temporarily rename the `main` function you want to
run as `main` before compiling._

## Step 2: Scenario A - Generating a `Vect` of a Given Length

Our first goal is to create a generator that produces a `Vect` of a specific length that we provide as an argument. To do this, we simply place the
argument _before_ the `Fuel` parameter in the signature.

**Define the generator**

The signature `(n : Nat) -> Fuel -> Gen MaybeEmpty (Vect n String)` tells `deriveGen`: "You will be _given_ a `Nat` named `n`. Your job is to produce a
`Vect` of that exact length."

```idris
genVectOfLen : Fuel -> (n : Nat) -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (VectString n)
genVectOfLen = deriveGen
```

### Test it

Let's write a `main` function to call our generator, providing `5` as the length.

```idris
runVect : IO ()
runVect = do
  putStrLn "--- Generating a Vect of a given length (5) ---"
  Just v <- pick (genVectOfLen (limit 10) 5)
    | Nothing => printLn "Generation failed"
  printLn v
```

### Compile and run

The output will show a `Vect` that always has exactly 5 elements, filled with random strings from the default `String` generator.

```text
--- Generating a Vect of a given length (5) ---
["a", "b", "c", "d", "e"]
The length is: 5
```

By placing `n` before `Fuel`, you have successfully commanded `deriveGen` to use it as a fixed input.

---

## Step 3: Scenario B - Generating a `Vect` of a Random Length

What if we don't want to provide a specific length? What if we want the generator itself to invent a random length? To do this, we use a **dependent
pair** in the return type.

**Define the generator**

The signature `Fuel -> Gen MaybeEmpty (n ** Vect n String)` tells `deriveGen`: "Your job is to first generate a random `Nat` (which you will call `n`),
and then generate a `Vect` of that length. When you are done, give me back both `n` and the `Vect`."

```idris
genRandomVect : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty (n ** VectString n)
genRandomVect = deriveGen
```

**Test It**

This time, when we call the generator, we don't provide a length. The generator will produce a pair containing the length it chose and the vector it
created.

```idris
runRandomVect : IO ()
runRandomVect = do
  putStrLn "--- Generating a Vect of a random length ---"
  for_ (the (List Int) [1..3]) $ \_ => do
    Just (n ** v) <- pick (genRandomVect (limit 10))
      | Nothing => printLn "Generation failed"
    printLn n
    printLn v
```

### Compile and run

You will see vectors of different, random lengths each time you run it.

```text
--- Generating a Vect of a random length ---
3
["a", "b", "c"]
0
[]
5
["d", "e", "f", "g", "h"]
```

By moving the parameter `n` from an input to a **generated** part of the output using the `**` syntax, you have completely changed `deriveGen`'s
behavior.

---

## Step 4: The Flexible Generator - Combining Patterns

Let's combine the patterns we've learned. Our first generator is flexible enough: it is taking a `Nat` as a _given_ input, but it is also taking an
_external generator_ hint for the element type using the `=>` syntax which will be overridden by the following exapmple.

**Test It**

To call this generator, we must provide both the length `n` and an element generator via the `@` syntax.

```idris
runFlexi : IO ()
runFlexi = do
  putStrLn "--- Generating a Vect of length 7 with overridden Str generator ---"
  let myStrGen = \fuel => elements ["A", "B", "C"] -- Our custom generator for the elements
                                                   -- It is created manually, so no need to use `fuel`.

  Just v <- pick (genVectOfLen (limit 10) 7 @{myStrGen})
    | Nothing => printLn "Generation failed"
  printLn v

  Just v' <- pick (genVectOfLen (limit 10) 7 @{genStr})
    | Nothing => printLn "Generation failed"
  printLn v'
```

### Compile, run, and observe

You will see a `Vect` of length 7, filled with numbers between 100 and 200, proving that `deriveGen` correctly used both your given length and your
external generator.

```text
--- Generating a Vect of length 7 with overridden Str generator ---
["A", "C", "B", "A", "A", "A", "C"]
["b", "c", "f", "a", "b", "b", "h"]
```

---

## Next Steps

Now that you know how to control `deriveGen` through signatures, you are ready for more advanced topics:

- **Want to understand how recursion affects generation?** Continue to **[Beyond Fuel: Structural Recursion](t07-beyond-fuel.md)** to learn about
`SpendingFuel` vs `StructurallyDecreasing` recursion.
- **Want to generate types with proof constraints?** Continue to **[Generating GADTs with Proofs](t08-generating-gadts-with-proofs.md)** to see how
`deriveGen` handles types like `SortedList`.
