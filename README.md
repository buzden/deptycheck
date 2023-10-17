<!-- idris
module README

import Data.Fin
import Data.List1

import Deriving.DepTyCheck.Gen

import Test.DepTyCheck.Gen

%default total

%language ElabReflection
-->

# DepTyCheck

[![Build and test](https://github.com/buzden/deptycheck/actions/workflows/ci-deptycheck.yml/badge.svg?branch=master)](https://github.com/buzden/deptycheck/actions/workflows/ci-deptycheck.yml)
[![Lint](https://github.com/buzden/deptycheck/actions/workflows/ci-super-linter.yml/badge.svg?branch=master)](https://github.com/buzden/deptycheck/actions/workflows/ci-super-linter.yml)
[![Documentation Status](https://readthedocs.org/projects/deptycheck/badge/?version=latest)](https://deptycheck.readthedocs.io/en/latest/?badge=latest)

A library for property-based testing with dependent types and automatic derivation of generators for Idris 2

## Status

🚧 The library is under heavy construction 🚧

For now, it lacks most of things required for normal property-based testing,
like support for *properties* and fancy testing operations.
Also, for now we do not support such important thing as *shrinking*.

The current focus for now is on *test data generators* and *automatic derivation* of them.

## Generators

Generators in the simplest case produce a bunch of values of appropriate type:

```idris
genSomeStrings : Gen NonEmpty String
genSomeStrings = elements ["one", "two", "three"]
```

You can combine several generators into one:

```idris
genMoreStrings : Gen NonEmpty String
genMoreStrings = oneOf [genSomeStrings, elements ["more", "even more"]]
```

> [!NOTE]\
> All generators listed in `oneOf` are meant to be distributed uniformly between each other as a whole thing.
> That is, in `genMoreStrings` values `"one"`, `"two"` and `"three"` have the same probability to be generated
> and this probability is `2/3` of probability for `"more"` or `"even more"` to appear.

So, the following generator is **not** equivalent to the `genMoreStrings` from above:

```idris
genMoreStrings' : Gen NonEmpty String
genMoreStrings' = elements ["one", "two", "three", "more", "even more"]
```

In `genMoreStrings'` all values are distributed uniformly.

To achieve the same result with reusing `genSomeStrings` generator, we need to dig into it deeper with `alternativesOf` function:

```idris
genMoreStrings'' : Gen NonEmpty String
genMoreStrings'' = oneOf $ alternativesOf genMoreStrings ++ alternativesOf (elements ["more", "even more"])
```

> [!NOTE]\
> There are also functions based on the `alternativesOf`, allowing to map values from all alternatives in a single expression
> named `mapAlternativesOf` and `mapAlternativesWith`.

You can also operate with alternatives as with applicative functors or monads.

For example, consider a generator of lists with length not greater than given.
There are a lot of possible implementations, but consider a recursive one:

```idris
genListsN : Gen NonEmpty a -> (n : Nat) -> Gen NonEmpty $ List a
genListsN _    Z     = [| [] |]
genListsN genA (S n) = oneOf $ [| [] |]
                            :: [| [genA] :: alternativesOf (genListsN genA n) |]
```

Distribution of lengths of lists produced by this generator is uniform,
thanks to `alternativesOf` function.

> [!NOTE]\
> If we were not using `alternativesOf` at all (say, with expression `[| genA :: genListsN genA n |]`),
> probability of getting a list of length `n+1` would be 2 times *less* than getting a list of length `n`.

Generators can be combined with operations from `Applicative` interface:

```idris
data X = MkX String String

genStrPairs : Gen NonEmpty X
genStrPairs = [| MkX genSomeStrings genMoreStrings |]
```

> [!NOTE]\
> The number of alternatives acquired by `alternativesOf` function of an applicative combination
> of two generators is a product of numbers of alternatives of those generators.

Unlike, say, in QuickCheck, generators can be empty.
This is important for dependent types.
For example, `Fin 0` is not inhabited,
thus we need to have an empty generator
if we want to have a generator for any `Fin n` (and sometimes we really want):

```idris
genFin : (n : Nat) -> Gen MaybeEmpty $ Fin n
genFin Z     = empty
genFin (S n) = elements' $ allFins n
```

As you can see from examples above,
there is a special marking of generator's emptiness in the first type argument of the `Gen` type.

Generators are also monads:

```idris
genAnyFin : Gen MaybeEmpty Nat => Gen MaybeEmpty (n ** Fin n)
genAnyFin @{genNat} = do
  n <- genNat
  f <- genFin n
  pure (n ** f)
```

Distribution of a generator built by monadic bind is such that
the whole continuation (i.e. RHS of `>>=`) applied to some `x` has the same probability to produce the result
as the probability for `x` to appear.

Thus, in the example above probability of particular natural `n` to come in the result
is the same as probability of this `n` to come on the given `genNat`.
After that, all fins for each particular `n` are distributed evenly, because it is a property of `genFin`.

You need to use `alternativesOf` if you want all possible resulted values to be distributed evenly, e.g.:

```idris
genAnyFin' : Gen MaybeEmpty Nat => Gen MaybeEmpty (n ** Fin n)
genAnyFin' @{genNat} = oneOf $ do
  n <- alternativesOf genNat
  f <- alternativesOf $ genFin n
  pure (n ** f)
```

Here we are using special monadic syntax support for lists of generators produced by `alternativesOf` function.

In the last example, all results of `genFin 1` and all results of `genFin 2` would **not** be distributed equally
in the case when `genNat` is `elements [1, 2]`, when they are distributed equally in the example of `genAnyFin`.
I.e., particular generator's application `genAnyFin @{elements [1, 2]}` would be equivalent to `oneOf [pure (1**0), elements [(2**0), (2**1)]]`
where `genAnyFin' @{elements [1, 2]}` would be equivalent to `elements [(1**0), (2**0), (2**1)]`.
Thus, they have the same domain, but different distributions.

<!-- idris
app_non_even, app_non_even_inlined, app_even, app_even_inlined : Gen MaybeEmpty (n ** Fin n)
app_non_even = genAnyFin @{elements [1, 2]}
app_non_even_inlined = oneOf [pure (1**0), elements [(2**0), (2**1)]]
app_even = genAnyFin' @{elements [1, 2]}
app_even_inlined = elements [(1**0), (2**0), (2**1)]
-->

Despite monadic bind of generators interprets left-hand side generators as a whole,
it looks inside it when the resulting generator is being asked for alternatives by `alternativesOf` function or its variants.

For example, `alternativesOf` being applied to `genAnyFin @{elements [1, 2]}` would produce two alternatives.
Sometimes this can be undesirable, thus, a `forgetAlternatives` function exists.
It allows to forget actual structure of a generator in terms of its alternatives.

Consider one more alternative of `genAnyFin`, now the given `genNat` is wrapped with `forgetAlternatives`:

```idris
genAnyFin'' : Gen MaybeEmpty Nat => Gen MaybeEmpty (n ** Fin n)
genAnyFin'' @{genNat} = do
  n <- forgetAlternatives genNat
  f <- genFin n
  pure (n ** f)
```

In this case, `alternativesOf` being applied to `genAnyFin'' @{elements [1, 2]}` would return a single alternative.

<!-- idris
main_genAnyFin_alternatives_count_corr : IO ()
main_genAnyFin_alternatives_count_corr = putStrLn $ show $ length (alternativesOf $ genAnyFin @{elements [1, 2]}) == 2

main_genAnyFin''_alternatives_count_corr : IO ()
main_genAnyFin''_alternatives_count_corr = putStrLn $ show $ length (alternativesOf $ genAnyFin'' @{elements [1, 2]}) == 1
-->

> [!NOTE]\
> Search for alternatives through the series of monadic binds can go to the first generator that
> is produced with no alternatives.
>
> Consider three generators:
>
> - `do { e1 <- elements [a, b, c]; e2 <- elements [d, e, f]; pure (e1, e2) }`
> - `do { e1 <- elements [a, b, c]; e2 <- forgetAlternatives $ elements [d, e, f]; pure (e1, e2) }`
> - `do { e1 <- forgetAlternatives $ elements [a, b, c]; e2 <- elements [d, e, f]; pure (e1, e2) }`
>
> The first two generators would have three alternatives each when inspected by `alternativesOf`,
> where the third one would have only one.
>
> But if you do `alternativesOf` for each of generators returned by the first `alternativesOf` and concatenate the results,
> the first example would give you nine alternatives, where the second one still would give you three.
> You can use `deepAlternativesOf` function with depth argument of `2` for this.
>
> This, actually, violates monadic laws in some sense.
> Say, `alternativesOf` can distinct between `pure x >>= f` and `f x` if generator `f x` is, say, of form `elements [a, b, c]`,
> because in the first case it would produce a single alternative, when in the second there will be three of them.
> However, according to the generated result these two generators shall be equivalent.

<!-- idris
namespace ForgetStructureNote

  a, b, c, d, e, f : Nat
  a = 0
  b = 1
  c = 2
  d = 3
  e = 4
  f = 5

  g1, g2, g3 : Gen NonEmpty (Nat, Nat)
  g1 = do { e1 <- elements [a, b, c]; e2 <- elements [d, e, f]; pure (e1, e2) }
  g2 = do { e1 <- elements [a, b, c]; e2 <- forgetAlternatives $ elements [d, e, f]; pure (e1, e2) }
  g3 = do { e1 <- forgetAlternatives $ elements [a, b, c]; e2 <- elements [d, e, f]; pure (e1, e2) }

  export
  main_forgetAlternatives_note_ex1_alternatives_count_corr : IO ()
  main_forgetAlternatives_note_ex1_alternatives_count_corr = putStrLn $ show $ 3 == length (alternativesOf g1)

  export
  main_forgetAlternatives_note_ex2_alternatives_count_corr : IO ()
  main_forgetAlternatives_note_ex2_alternatives_count_corr = putStrLn $ show $ 3 == length (alternativesOf g2)

  export
  main_forgetAlternatives_note_ex3_alternatives_count_corr : IO ()
  main_forgetAlternatives_note_ex3_alternatives_count_corr = putStrLn $ show $ 1 == length (alternativesOf g3)

  export
  main_forgetAlternatives_note_ex1_alternatives_sq_count_corr : IO ()
  main_forgetAlternatives_note_ex1_alternatives_sq_count_corr = putStrLn $ show $ 9 == length (deepAlternativesOf 2 g1)

  export
  main_forgetAlternatives_note_ex2_alternatives_sq_count_corr : IO ()
  main_forgetAlternatives_note_ex2_alternatives_sq_count_corr = putStrLn $ show $ 3 == length (deepAlternativesOf 2 g2)

  export
  main_forgetAlternatives_note_ex3_alternatives_sq_count_corr : IO ()
  main_forgetAlternatives_note_ex3_alternatives_sq_count_corr = putStrLn $ show $ 3 == length (deepAlternativesOf 2 g3)
-->

> [!NOTE]\
> Please notice that `deepAlternativesOf` can "see" through `forgetAlternatives`, so count of deep alternatives of depth `2`
> for the third case would still be `3`.
> If you really need to hide the full structure even from the `deepAlternativesOf`, you can be much stronger version called
> `forgetStructure`:
>
> - `do { e1 <- forgetStructure $ elements [a, b, c]; e2 <- elements [d, e, f]; pure (e1, e2) }`
>
> This this case both `alternativesOf` and even `deepAlternativesOf` would give you the single alternative.
> But please keep in mind that monadic composition of a generator with forgotten structure and some significantly empty generator function
> (like `oneOf [g1, forgetStrcuture g2 >>= f]`) may have unexpected distribution of values.
> Probability of values produced by the `f` related to the probability of values produced by `g1` may be divided by the
> probability of the generator `forgetStructure g2 >>= f` to produce a non-empty value.
>
> When you are using the weaker `forgetAlternatives` instead of `forgetStructure`, distributions are more predictable
> in case when `g2` has some non-trivial structure of alternatives.

<!-- idris
namespace ForgetStructureNote

  g4 : Gen NonEmpty (Nat, Nat)
  g4 = do { e1 <- forgetStructure $ elements [a, b, c]; e2 <- elements [d, e, f]; pure (e1, e2) }

  export
  main_forgetAlternatives_note_ex4_alternatives_count_corr : IO ()
  main_forgetAlternatives_note_ex4_alternatives_count_corr = putStrLn $ show $ 1 == length (alternativesOf g4)

  export
  main_forgetAlternatives_note_ex4_alternatives_sq_count_corr : IO ()
  main_forgetAlternatives_note_ex4_alternatives_sq_count_corr = putStrLn $ show $ 1 == length (deepAlternativesOf 2 g4)
-->

Also, here you can see that we can use generators as `auto`-parameters,
thus no need in a separate thing like QuickCheck's `Arbitrary`.

You can also see that having a dependent type to generate,
we can consider different ratio between given and generated type arguments.
Technically speaking, `Fin n` and `(n ** Fin n)` are different types,
but pragmatically, `genFin` and `genAnyFin` both generate elements of type `Fin n`,
but the first one takes `n` as a given value,
and the second one generates value for the type argument along with the main value.

You can read more on the design of generators in [documentation](https://deptycheck.readthedocs.io/en/lastest/explanation/generators/).

## Derivation of generators

DepTyCheck supports automatic derivation of generators using the datatype definition.

For now, it is not tunable at all, however, it is planned to be added.

Derived generators are total.
Since for now generators are finite,
it was decided to use explicit fuel pattern to support recursive data types.
For simplicity, fuel pattern is used for all derived generators.

To invoke derivation, we use `deriveGen` macro:

```idris
genNat : Fuel -> Gen MaybeEmpty Nat
genNat = deriveGen
```

It uses very powerful metaprogramming facility of Idris 2 programming language
for analysing the data structure which generator is derived for and producing code of the asked generator at compile time.
This facility is called *elaborator reflection*, and you can find some kind of tutorial for this
[here](https://github.com/stefan-hoeck/idris2-elab-util/blob/main/src/Doc/Index.md).
To enable it, you have to add `%language ElabReflection` to the source code before the first call to the macro.

However, beware of possible high resources consumption of this stage.
In our non-trivial examples, derivation may take several hours and tens of gigabytes of memory.
We work for improvements of this, however we hope that
[new core](https://github.com/edwinb/Yaffle/) of the Idris compiler would solve this issue completely.

Of course, we do not support all possible dependent types.
For example, for now, we do not support type-polymorphic types and
GADTs which have function calls in type indices of their constructors.
However, we are constantly working for widening supported types.

> [!NOTE]\
> For now, derivation is supported only for `MaybeEmpty` generators.

<!-- Example of non-trivial derivation should go here -->

More on design of derivator can be found in [documentation](https://deptycheck.readthedocs.io/en/latest/explanation/derivation/).

## Usage and installation

For building and testing we use [`pack`](https://github.com/stefan-hoeck/idris2-pack/) package manager.

> [!NOTE]\
> Notice, that we've gone mad as far as possible, so even calling for makefile of Sphinx for building documentation
> is done through `pack` and `prebuild` action inside an appropriate `ipkg` file.
>
> Despite that, to make [LSP](https://github.com/idris-community/idris2-lsp) working well,
> only a single code-related `ipkg` file is left in the top-level folder of the project.

The main `pack`'s collection we test against is in the file called [`.pack-collection`](/.pack-collection) in the root of this repository.
Also, we test against the latest pack collection nightly.

We try to use as fresh version of the Idris 2 compiler as possible.
But, we depend on particular features, like [this PR](https://github.com/idris-lang/Idris2/pull/2791),
so we may set specific compiler version in the local `pack.toml` file.

Similar thing happens with couple of thirdparty dependencies.
For example, we didn't manage to migrate [one big overhaul](https://github.com/stefan-hoeck/idris2-elab-util/pull/56) of the `elab-util` package,
thus we maintain a pre-overhaul fork with necessary compatibility updates.
These versions are also set in the local `pack.toml` configuration file.

Due to the stuff above, DepTyCheck is not yet committed to the pack collection.
If you plan to use it, you need to copy particular versions of the compiler and dependencies
from the library's `pack.toml` to a local `pack.toml`.
