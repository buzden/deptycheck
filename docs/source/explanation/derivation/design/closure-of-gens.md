<!-- idris
module Explanation.Derivation.Design.ClosureOfGens

import Explanation.Derivation.Design

%language ElabReflection
-->

# Closure of derived generators

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
genX : Fuel -> Gen MaybeEmpty X
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
genX : Fuel -> Gen MaybeEmpty X
genX fuel = data_X fuel
  where
    data_X : Fuel -> Gen MaybeEmpty X
    data_Y : Fuel -> Gen MaybeEmpty Y
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
now function of type `Fuel -> Gen MaybeEmpty Y` would be derived twice,
both times as a local function of derived generator for particular derivation task.

This is done because each call to the `deriveGen` macro is fully independent.
No state is shared between calls to macros.
In the future, such derived generators caching can be implemented either by implementing some state sharing in the compiler,
or with changing the way which derivation task is expressed (for now, this is the call to the `deriveGen` macro).
Maybe, some bunched derivation macro should be also considered,
this would give user a way to express where derived generators should be shared and where should not.

:::{note}
There is one problem with such bunched generation, though.
It looks at the first glance as very technical, however, it has one much more fundamental problem deep inside.

The current derivation metaprogram (entered with a macro `deriveGen`)
gets the type of generator-to-be-derived through the type of expression at the macro's use site.
I.e. depending on the type of expression `deriveGen`, it will derive different generators.
This is a way of passing type argument to an elaboration script and works well with any kind of types.

However, if we want to perform bunched or cached derivation,
we will need some other mechanism of passing the type argument to an elaboration script.
Since Idris is a dependently typed language, there is a possibility to pass arguments of type `Type` as a regular argument.
Since Idris is based on QTT even type argument can be a "runtime", i.e. observable inside a function's body
(which is definitely needed during derivation).

But this approach has one unpleasant consequence,
namely that the type that is value of the "runtime" (i.e. observable) argument,
cannot have non-runtime (i.e. erased) arguments.
You can see some discussion in the compiler's [issue #2021](https://github.com/idris-lang/Idris2/pull/2021).
The digested idea is that the current {math}`\{0, 1, \omega\}` semiring which is selected as the parameter of QTT in Idris,
is not sufficient for a language with metaprogramming facility, because *erased* parameters notion splits into two:
one is for values that *must not* be present at runtime, the other is for values that are available only at the compile-time.
The first one cannot be exposed to runtime by elaboration script, the second can.

So, there is a need of research on more appropriate semiring that covers metaprogramming cases too.
Some work already is been doing by researchers (in particular by Andre Videla) but it may require additional efforts.
:::
