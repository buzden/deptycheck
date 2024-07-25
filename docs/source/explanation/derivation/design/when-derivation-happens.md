<!-- idris
module Explanation.Derivation.Design.WhenDerivationHappens

import Explanation.Derivation.Design

%language ElabReflection
-->

# When derivation happens

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

If a compiler or some library implements the first step, then this approach is the simplest way for the end user to write a derivation,
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
  current approaches with *sums of products* and Haskell's `Generic` do not support dependent types or even GADTs.

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
<!--
TODO to add a link to Idris documentation as soon as elaboration scripts are documented.
-->

Thus, DepTyCheck's derivation mechanism is a fully compile-time metaprogram that analyses generated datatype and
produces generator's code which is checked for type correctness and totality right after.
