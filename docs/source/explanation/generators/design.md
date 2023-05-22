<!-- idris
import Data.Vect

import Test.DepTyCheck.Gen
-->

# Design of generators

(sect-gen-general-design)=

## What is a generator

Different property-based testing libraries have slightly different notions of generators.
The common beside the purely functional ones is that generator is a polymorphic type that
has a way to compute a value of type `a` out of generator of `a` being possibly given some context.

:::{todo}
Generator on very high level of abstraction is a calculation of a value (or values) of some particular type in particular context.
:::

:::{todo}
comparison to the design of QuickCheck and Hedgehog (in particular, in shrinking)
:::

We are working in dependently typed context, so in general case generator is a function
rather than just a data value.

## `Gen` used as interface

### Context: `Gen`-`Arbitrary` duality in QuickCheck

Haskell's property-based testing founder, [QuickCheck](https://hackage.haskell.org/package/QuickCheck),
has distinction between `Gen` datatype and `Arbitrary` typeclass.
Both are, in a sense, generators of values but they are playing different roles.

Particular `Gen`'s, being a datatype, are first-class citizens, i.e. can be passed to and returned from functions.
This gives an ability to have combination and transformation functions upon `Gen`'s,
including those that have different generators of similar type as parameters.
Consider, for example, a function that combines values of two generators according to the semigroup operation:

```haskell
semGens :: Semigroup a => Gen a -> Gen a -> Gen a
semGens x y = (<>) <$> x <*> y
```

In its turn, `Arbitrary` is a typeclass.
There is a single such definition for a type (unless you go with incoherency magic).
In a sense, it is a *canonic generator* for a type.
:::{note} QuickCheck's `Arbitrary` has also a function of shrinking explained [above](sect-gen-general-design).
:::
So, there is no need to pass it explicitly down to functions, once it is present in the signature.
Consider the following recursive function:

```haskell
listOfLength :: Arbitrary a => Int -> Gen [a]
listOfLength n | n <= 0    = pure []
               | otherwise = (:) <$> arbitrary <*> listOfLength (n - 1)
```

:::{note}
Property-based libraries with integrated shrinking, like [Hedgehog](https://hackage.haskell.org/package/hedgehog),
may have no typeclass like `Arbitrary`.
:::

### Universal `Gen` in DepTyCheck

In Idris 2, though, there is no need of distinction like above because implementations of interfaces passed to a function are
[special kind](https://idris2.readthedocs.io/en/latest/updates/updates.html#auto-implicits-and-interfaces),
of usual implicit parameters (`auto`-parameters) thus they are first-class citizens too.

So, we can pass generators both explicitly or as `auto`-parameters.
DepTyCheck's type `Gen` plays roles of both *just generators* and *canonical generators* being passed as
an ordinary or an `auto`-parameter respectively.

Consider functions, analogues to above QuickCheck-based ones, but using DepTyCheck:

```idris
semGens : Semigroup a => {em : _} -> Gen em a -> Gen em a -> Gen em a
semGens x y = [| x <+> y |]

listOfLength : {em : _} -> (genA : Gen em a) => Nat -> Gen em (List a)
listOfLength Z     = pure []
listOfLength (S n) = [| genA :: listOfLength n |]
```

<!-- idris
vectOfLength : {em : _} -> (genA : Gen em a) => (n : Nat) -> Gen em (Vect n a)
vectOfLength Z     = pure []
vectOfLength (S n) = [| genA :: vectOfLength n |]
-->

:::{note}
Please, notice that DepTyCheck's `Gen` type contains an additional type argument,
which stands for emptiness markup.
For instance, `Gen MaybeEmpty a` is a possibly empty generator of values of type `a`,
where `Gen NonEmpty a` is a definitely non-empty generator.
For details, see [below](sect-gen-emptiness).
:::

(sect-gen-emptiness)=

## Can generator be empty?

:::{todo} why generators must support emptiness (take example from the readme)
:::

:::{todo} emptiness marking preservation in combinations
:::

:::{todo} "type aliases" for most useful generators types (two of three, ha-ha)
:::

## Result of generation

:::{todo} Value, or maybe value (depending on emptiness)
:::

:::{todo} Random nature of generation
:::

(sect-gen-totality)=

## Totality of generation

:::{todo} finiteness of generators
:::

(sect-fuel-pattern-workaround)=

### Fuel pattern workaround

:::{todo} fuel-pattern as a workaround for infinite datatypes
:::
