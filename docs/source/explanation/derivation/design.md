<!-- idris
module Explanation.Derivation.Design

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

-- Empty body derivation
DerivatorCore where
  canonicBody sig n = pure [ callCanonic sig n implicitTrue (replicate _ implicitTrue) .= `(empty) ]
-->

# Design of derivation

By *derivation* we mean automatic creation of a generator given a datatype definition and,
possibly, some configuration and additional stuff.

:::{todo}
Almost every section here should have a reference to some section in `reference/contributors` for technical explanations.
:::

## When derivation happens

In principle, derivation can happen both at *runtime* or at the *compile time*.

Compile time code involves some kind of *metaprogramming*, *macros*, *compiler plugins* or
some other special support of intervention to the compilation process.

In contrast, runtime code is conceptually simpler (because it is an ordinary code)
but it requires some kind of runtime reflection of datatype definitions, which is not supported by Idris (or e.g. Haskell).
:::{note}
Being based on QTT, Idris supports matching on types which can be seen as a kind of runtime reflection of *types*.
However, this does not give an ability to inspect *definitions* of these types,
thus this facility does not give an ability to implement runtime derivation of generators.
:::

Also, a hybrid approach exists, when the task of derivation based on the datatype definition is split into two stages:

- compile-time derivation of transformations to and from some *universal intermediate representation*, and
- usual higher-order runtime function that does derivation being given an instance of this universal intermediate representation.

If a compiler or some library implements the first step, then this approach is the simplest way for the end-user to write a derivation,
because there is a need to implement only the second step using regular code, without deep dive into metaprogramming details.

This hybrid approach is widely used, for example

- Haskell's QuickCheck
  [simple](https://hackage.haskell.org/package/generic-arbitrary) or
  [tunable](https://hackage.haskell.org/package/generic-random)
  generators derivation which uses compiler-aided
  [generic representation](https://hackage.haskell.org/package/base/docs/GHC-Generics.html) of data types;
- [Haskell](https://hackage.haskell.org/package/generics-sop) and [Idris](https://github.com/stefan-hoeck/idris2-sop) libraries for
  generic programming that uses [sums of products](https://www.andres-loeh.de/TrueSumsOfProducts/) as the universal intermediate representation.

However, this approach has its own drawbacks:

- since the second step is a runtime step, all transformations to and from an intermediate representation are performed at runtime too,
  which negatively affects performance;
- in totality-controlled languages, there may be problems with recursive datatypes;
  since two steps are independent, their totality is checked independently;
  however, the first step is usually implemented for all types at once, thus this translation cannot be proven total even
  if the resulting chain of steps could be;
- universal intermediate representation must be powerful enough to represent all datatypes that can be used for the final derivation;
  current approaches with *sums of products* and Haskell's ``Generic`` do not support dependent types or even GADTs.

:::{note}
There exists an approach that bites the first drawback (and possibly, the second one too),
it is called "[staged derivation](https://mpickering.github.io/papers/staged-sop.pdf)".
In principle, it is the same two-stage approach with a difference that the second stage is performed at the compile time
while being written in the simple style as if runtime code.
This approach is very perspective, however, it still uses sums of products as an intermediate representation,
thus inapplicable directly for dependent types.
:::

Since, we focus on total generators for dependent types, we cannot rely on common hybrid approach.
Considering all said above, it is decided to go the hard way and to do derivation of generators directly,
using metaprogramming facility if Idris called *elaboration scripts*.
% TODO to add a link to Idris documentation as soon as elaboration scripts are documented.

Thus, DepTyCheck's derivation mechanism is a fully compile-time metaprogram that analyses generated datatype and
produces generator's code which is checked for type correctness and totality right after.

(sect-derivation-task)=

## Derivation task

We call an information given to a request of a DepTyCheck library user for derivation of a generator a *derivation task*.
Technically this request is done through a call to [a macro function](ref-deriveGen) or to [an elaboration script](ref-deriveGenExpr).
This information is technically given through a type signature of the macro result type or an explicit parameter of the elaboration script.
But *semantically* this information contains the following:

- the target, i.e. type or type constructor for which a generator is derived;
- if the target is a type constructor, then for each of its type arguments,
  information of whether the value of it is given or should be generated;
- external subgenerators, i.e. set of derivation tasks whose generators can be looked at the generation-site
  if a value of specific type is needed.

Also, some additional candidates were considered, but were temporarily put to the [backlog](tbd):

- support of additional (arbitrary) `auto`-parameters of generator function;
- list of external subgenerators (or derivation tasks for subgenerators) which are available at the derivation-site;
- various configuration options for tuning distribution and ways of combining subgenerators.

:::{note}
Besides stuff for a derivation task, derived type signature contains also a special `Fuel` argument.
This is done as a workaround of [a temporary design decision](sect-fuel-pattern-workaround) on `Gen` monad
to support derivation for potentially infinite data structures.
:::

There are some examples of derivation tasks and corresponding generator signatures.

:::{todo}
We definitely need more examples of particular derivation tasks and corresponding signatures here.

Examples should contain:

- trivial examples for non-recursive data type with no type arguments;
- examples for recursive data type with no type arguments, like `Nat`;
- examples for a data type with some non-dependent type arguments (i.e. when no type argument does not depend on another);
  all variants of "all given", "all generated", "some given, some generated" should be present;
- example for a data type with dependent type arguments.
:::

(sect-type-indices)=

## Type parameters and type indices

### Distinction between the two

Not a surprise, datatypes can have *type arguments*.
Consider an `Either` datatype with two of them:

<!-- idris
%hide Prelude.Either
-->

```idris
data Either a b = Left a | Right b
```

This has a lot of use in *generic programming*; you can have *polymorphic functions* that act on data disregarding particular type arguments.
For example, you can map over values inside the `Either`:

```idris
bimap : (a -> c) -> (b -> d) -> Either a b -> Either c d
bimap f _ (Left x)  = Left  (f x)
bimap _ g (Right y) = Right (g y)
```

Such type of type arguments is called *type parameters*.
Such data and functions are *parametric* on these parameters,
because they behave in the same way given any types for the parameters.

However, in richer type systems (which support dependent types or at least GADTs) types can be *indexed*.
Consider a classical example of constant-size vectors:

<!-- idris
%hide Data.Vect.Vect
-->

```idris
data Vect : Nat -> Type -> Type where
  Nil  :                  Vect 0       a
  (::) : a -> Vect n a -> Vect (1 + n) a
```

In this case, the second type argument is still a parameter, it is same in all constructors.
However, the first type argument is an *index*.
Depending on the value of this index, the set of available constructors can differ.

For example, once you known that the size of the vector is greater than zero,
you do not need to match on the `Nil` constructor.
In these examples, all matches are against the `(::)` constructor:

<!-- idris
%hide Data.Vect.head
%hide Data.Vect.last
-->

```idris
head : Vect (1 + n) a -> a
head (x :: _) = x

last : Vect (1 + n) a -> a
last (x :: Nil)       = x
last (_ :: tl@(_::_)) = last tl
```

So, value of type parameter cannot influence on the set of available data constructors,
but the value of type index can.

### Relativity of the type index status

:::{todo}
relativity of these terms to the derivation task
:::

## Closure of derived generators

Datatype for which generator is derived can contain some other datatypes as parts.
There is a need to have generators for them in the case when these generators are not present as external in the derivation task.
Notice also, that these datatypes can be mutually recursive and we need to tackle this also during derivation.

That is why single derivation task actually produces a closure of generators.
And since they can be mutually recursive, then in the derived code all function signatures goes before all function bodies.

For example, consider the following data structure and the following derivation task.

```idris
mutual
  data X = X0 | X1 | X2 Y
  data Y = Y0 | Y1 X
```

<!-- idris
namespace GenCloj_DerivTask {
-->
```idris
genX : Fuel -> Gen X
genX = deriveGen
```
<!-- idris
  }
-->

In this case, derived generator function would have the following structure.

<!-- idris
namespace GenCloj {
-->
```idris
genX : Fuel -> Gen X
genX fuel = data_X fuel
  where
    data_X : Fuel -> Gen X
    data_Y : Fuel -> Gen Y
    data_X fuel = ?xs_gen_body
    data_Y fuel = ?ys_gen_body
```
<!-- idris
  }
-->

:::{note}
Here and below we leave holes like `?xs_gen_body` for the code that is actually derived but which derivation process is explained below.
:::

:::{todo}
Maybe, more realistic example, e.g. alternating list of e.g. `Nat`s and `String`s.
:::

The current design decision is that all subgenerators that are derived for the particular derivation task
are local to the function for that derivation task.
That is, if some other derivation task will need a derived generator for the datatype `Y`,
now function of type `Fuel -> Gen Y` would be derived twice, both times as a local function of derived generator for particular derivation task.

This is done because each call to the `deriveGen` macro is fully independent.
No state is shared between calls to macros.
In the future, such derived generators caching can be implemented either by implementing some state sharing in the compiler,
or with changing the way which derivation task is expressed (for now, this is the call to the `deriveGen` macro).
Maybe, some bunched derivation macro should be also considered,
this would give user a way to express where derived generators should be shared and where should not.

## Design of a single generator

Generator of a single type simply attempts to call for all possible constructors of this type (in the given context of the derivation task).

:::{note}
This design decision is temporary.
In the future it is planned to be configurable.
For example, one may want to tune possibilities of different constructors.

It is crucial.
Consider derived simple generator for the `Nat` type.
Probability of `Z` and `S` cases are equal.
It means that probabilities of zero and all numbers more than zero (in bounds of given fuel) are equal,
probabilities of `1` and all numbers more than `1` are equal too, and etc.
:::

It is decided that this place is the only where fuel of the fuel pattern is spent.
It means that potentially infinite recursion and empty fuel should be managed only here,
so there is no need to bother on this in functions that generate values for particular constructors.

To make derived generators to be provably total, target datatypes are analysed for recursion.
Non-recursive paths are called always even if given `Fuel` value is `Dry`.
Recursive constructors are called only when `Fuel` can be spent.

So, expanding the example from above, the following code would be derived.

<!-- idris
namespace SingleGen {
-->
```idris
genX : Fuel -> Gen X
genX fuel = data_X fuel
  where
    data_X : Fuel -> Gen X
    data_Y : Fuel -> Gen Y

    data_X fuel = case fuel of
        Dry    => oneOf' [con_X0 Dry, con_X1 Dry]
        More f => oneOf' [con_X0 f  , con_X1 f  , con_X2 f]
      where
        con_X0 : Fuel -> Gen X
        con_X1 : Fuel -> Gen X
        con_X2 : Fuel -> Gen X

        con_X0 fuel = ?gen_body_for_constructor_X0
        con_X1 fuel = ?gen_body_for_constructor_X1
        con_X2 fuel = ?gen_body_for_constructor_X2

    data_Y fuel = case fuel of
        Dry    => oneOf' [con_Y0 Dry]
        More f => oneOf' [con_Y0 f  , con_Y1 f]
      where
        con_Y0 : Fuel -> Gen Y
        con_Y1 : Fuel -> Gen Y

        con_Y0 fuel = ?gen_body_for_constructor_Y0
        con_Y1 fuel = ?gen_body_for_constructor_Y1
```
<!-- idris
  }
-->

## Derivation for a single constructor

### Simple case

In a simple case when there are no type indices and no dependent types are present,
derived code for generation of a value for a single constructor is also simple.
Generation can be boiled down to calling to subgenerators and then calling the selected constructor.
Finishing the example from above, we could derive something like the following.

<!-- idris
namespace SingleCon_Simple {
-->
```idris
genX : Fuel -> Gen X
genX fuel = data_X fuel
  where
    data_X : Fuel -> Gen X
    data_Y : Fuel -> Gen Y

    data_X fuel = case fuel of
        Dry    => oneOf' [con_X0 Dry, con_X1 Dry]
        More f => oneOf' [con_X0 f  , con_X1 f  , con_X2 f]
      where
        con_X0 : Fuel -> Gen X
        con_X1 : Fuel -> Gen X
        con_X2 : Fuel -> Gen X

        con_X0 fuel = [| X0               |]
        con_X1 fuel = [| X1               |]
        con_X2 fuel = [| X2 (data_Y fuel) |]

    data_Y fuel = case fuel of
        Dry    => oneOf' [con_Y0 Dry]
        More f => oneOf' [con_Y0 f  , con_Y1 f]
      where
        con_Y0 : Fuel -> Gen Y
        con_Y1 : Fuel -> Gen Y

        con_Y0 fuel = [| Y0               |]
        con_Y1 fuel = [| Y1 (data_X fuel) |]
```
<!-- idris
  }
-->

As you can see, the power of `Applicative` interface is enough for building more complex generators out of subgenerators.

But, actually, this is the case only when we do not consider dependently typed data.
We have to use monadic interface when some of constructor's arguments depend on each other.

Also, there are issues on non-determinism in the order of such generation, which will be explained below.
Because all of that, and for the sake of simplicity of the derivation mechanism,
actual derived code slightly differ even for the simple case.
The following code would be derived.

<!-- idris
namespace SingleCon_Full {
-->
```idris
genX : Fuel -> Gen X
genX fuel = data_X fuel
  where
    data_X : Fuel -> Gen X
    data_Y : Fuel -> Gen Y

    data_X fuel = case fuel of
        Dry    => oneOf' [con_X0 Dry, con_X1 Dry]
        More f => oneOf' [con_X0 f  , con_X1 f  , con_X2 f]
      where
        con_X0 : Fuel -> Gen X
        con_X1 : Fuel -> Gen X
        con_X2 : Fuel -> Gen X

        con_X0 fuel = oneOf' [ pure X0 ]
        con_X1 fuel = oneOf' [ pure X1 ]
        con_X2 fuel = oneOf' [ do y <- data_Y fuel
                                  pure $ X2 y
                             ]

    data_Y fuel = case fuel of
        Dry    => oneOf' [con_Y0 Dry]
        More f => oneOf' [con_Y0 f  , con_Y1 f]
      where
        con_Y0 : Fuel -> Gen Y
        con_Y1 : Fuel -> Gen Y

        con_Y0 fuel = oneOf' [ pure Y0 ]
        con_Y1 fuel = oneOf' [ do x <- data_X fuel
                                  pure $ Y1 x
                             ]
```
<!-- idris
  }
-->

### Managing type indices

We are working with dependently typed data, which may have type indices.
:::{note}
[Remember](sect-type-indices) that set of available constructors may differ depending on the value of a type index.
Also, particular derivation task may influence in whether or not some type argument would be a type index.
:::

An arbitrary well-typed expression can be on the place of type index in a constructor's definition.
For now, we support only two cases: data constructors and values that are propositionally equal to some other type arguments.

#### Data constructor indices

There is no problem or much difference with the simple case from above in the case when type index is a generated value
according to the particular derivation task.
Consider the following indexed data type and a derivation task, where this index is generated.

```idris
data D : Bool -> Type where
  JJ : Nat ->    Nat -> D b
  FN : Nat ->    D b -> D False
  TL : String ->        D True
  TR : String -> D b -> D True
```

<!-- idris
namespace TypIdx_Gend_DerivTask {
-->
```idris
genD_idx_generated : Fuel -> (Fuel -> Gen Nat) => (Fuel -> Gen String) => Gen (b ** D b)
genD_idx_generated = deriveGen
```
<!-- idris
  }
-->

For this derivation task the following generator function would be derived.

<!-- idris
namespace TypIdx_Gend_DerivedExample {
-->
```idris
genD_idx_generated : Fuel -> (Fuel -> Gen Nat) => (Fuel -> Gen String) => Gen (b ** D b)
genD_idx_generated @{data_Nat} @{data_String} fuel = data_D_giv_no fuel
  where
    data_Bool : Fuel -> Gen Bool
    data_Bool fuel = case fuel of
        Dry    => oneOf' [con_True Dry, con_False Dry]
        More f => oneOf' [con_True f, con_False f]
      where
        con_True  : Fuel -> Gen Bool
        con_False : Fuel -> Gen Bool

        con_True  fuel = oneOf' [pure True]
        con_False fuel = oneOf' [pure False]

    data_D_giv_no : Fuel -> Gen (b ** D b)
    data_D_giv_no fuel = case fuel of
        Dry    => oneOf' [con_JJ Dry, con_TL Dry]
        More f => oneOf' [con_JJ f, con_FN f, con_TL f, con_TR f]
      where
        con_JJ : Fuel -> Gen (b ** D b)
        con_FN : Fuel -> Gen (b ** D b)
        con_TL : Fuel -> Gen (b ** D b)
        con_TR : Fuel -> Gen (b ** D b)

        con_JJ fuel = oneOf' [ do b  <- data_Bool fuel
                                  n1 <- data_Nat fuel
                                  n2 <- data_Nat fuel
                                  pure (_ ** JJ {b} n1 n2)
                             ]
        con_FN fuel = oneOf' [ do n        <- data_Nat fuel
                                  (b ** d) <- data_D_giv_no fuel
                                  pure (_ ** FN {b} n d)
                             ]
        con_TL fuel = oneOf' [ do s <- data_String fuel
                                  pure (_ ** TL s)
                             ]
        con_TR fuel = oneOf' [ do s        <- data_String fuel
                                  (b ** d) <- data_D_giv_no fuel
                                  pure (_ ** TR {b} s d)
                             ]
```
<!-- idris
  }
-->

:::{todo}
Example of data with boolean index, 4 constrs, one parametric, one for false, two for true
:::

#### Equality of index to another argument

#### Superposition of both

:::{todo}
Example of deep constructors index with propositional equality inside
:::

#### Other index expressions

:::{todo}
What we'd want to support, e.g. invertible single-argument functions
:::

### Strategies of constructor's arguments derivation

:::{todo}
incl. different strategies of constructor derivators
:::

#### Least-effort strategy

:::{todo}
least-effort strategy and the company
:::
