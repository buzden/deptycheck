<!-- idris
module README

import Data.Fin
import Data.List1

import Test.DepTyCheck.Gen
import Test.DepTyCheck.Gen.Auto

%default total

%language ElabReflection
-->

# DepTyCheck

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
genSomeStrings : Gen String
genSomeStrings = elements ["one", "two", "three"]
```

Generators can be combined with operations from `Applicative` and `Alternative` interfaces:

```idris
genMoreStrings : Gen String
genMoreStrings = genSomeStrings <|> elements ["more", "even more"]
```

```idris
data X = MkX String String

genStrPairs : Gen X
genStrPairs = [| MkX genSomeStrings genMoreStrings |]
```

Notice that distribution of simple elements listing can depend on the environment.
For example, the following generator is completely equivalent to `genMoreStrings` from above:

```idris
genMoreStrings' : Gen String
genMoreStrings' = elements ["one", "two", "three", "more", "even more"]
```

I.e., all five elements are distributed equally in the resulting generator.
To make the alternatives to be distributed equally as a whole, we can to make them *independent*:

```idris
genMoreStrings'' : Gen String
genMoreStrings'' = independent genMoreStrings <|> independent (elements ["more", "even more"])
```

Being `Alternative` (unlike, say, in QuickCheck) generators can be empty.
This is important for dependent types.
For example, `Fin 0` is not inhabited,
thus we need to have an empty generator if we want to have a generator for any `Fin n`:

```idris
genFin : (n : Nat) -> Gen $ Fin n
genFin Z     = empty
genFin (S n) = elements $ forget $ allFins n
```

Generators are also monads:

```idris
genAnyFin : Gen Nat => Gen (n ** Fin n)
genAnyFin @{genNat} = do
  n <- genNat
  f <- genFin n
  pure (n ** f)
```

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

<!-- idris
%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort
-->

DepTyCheck supports automatic derivation of generators using the datatype definition.

For now, it is not tunable at all, however, it is planned to be added.

Derived generators are total.
Since for now generators are finite,
it was decided to use explicit fuel pattern to support recursive data types.
For simplicity, fuel pattern is used for all derived generators.

To invoke derivation, we use `deriveGen` macro:

```idris
genNat : Fuel -> Gen Nat
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

<!-- Example of non-trivial derivation should go here -->

More on design of derivator can be found in [documentation](https://deptycheck.readthedocs.io/en/latest/explanation/derivation/).

## Usage and installation

We try to use as fresh version of the Idris 2 compiler as possible.
The version we test against is in the file called [`.idris-version`](/.idris-version) in the root of this repository.

Derivation facility of this library has en external dependency to the [`idris2-elab-util`](https://github.com/stefan-hoeck/idris2-elab-util/) package.
In order to run tests, you will also need [`idris2-sop`](https://github.com/stefan-hoeck/idris2-sop) package.

For building, installing and testing we have a makefile, thus we use simple old `make` utility to do this.
Installation is done with a built-in facility of the Idris 2 compiler,
so consult to [its documentation](https://idris2.readthedocs.io/en/latest/reference/packages.html?highlight=--install#using-package-files)
to see where the library is installed.
