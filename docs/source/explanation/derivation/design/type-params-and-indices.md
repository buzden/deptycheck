<!-- idris
module Explanation.Derivation.Design.TypeParamsAndIndices

import Explanation.Derivation.Design

%language ElabReflection
-->

(sect-type-indices)=

# Type parameters and type indices

## Distinction between the two

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

## Relativity of the type index status

:::{todo}
relativity of these terms to the derivation task
:::
