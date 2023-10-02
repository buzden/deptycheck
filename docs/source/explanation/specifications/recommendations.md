# Practical recommendations

This is a collection of principles,
thoughts and ideas that were developed based on the experience of writing DepTyCheck specifications for programming languages.
Some of them are incomplete, some highlight possible problems that don't have a good solution yet.
However, reading this could give you some thoughts and ideas regarding writing specifications.

## Basic outline of programming language's (static) semantics specification

The programming language specification is expressed as a set of (indexed) types that model the constructs of the language,
with additional semantic restrictions (and, possibly, some helper types used to ensure that restrictions hold).
Most of the language constructs exist withing certain context
(the set of available class definitions, the list of accessible variables, whether type of expression is inferrable, etc.).
This context can be represented as a set of indices of a type.
Then the changes to these contexts can be defined as applying constructors to the indices,
and the restrictions can be imposed via inductively defined predicates on the context values.

It should be noted that attempting to modify the context in a complex, function-like way, leads to signification performance degradation.
This was discovered after implementing a specification for a MiniJava subset
that featured tracking of variable initialization via a flag attached to a variable.
This article features a general outline of defining such mutations, however they should be used with caution.
It is better to be able to define the context in an constructo-application-only way, and generally keep the specification as concise as possible.

A good starting point of writing a specification is a language's grammar.
You could start by creating an empty type that will represent some construct and adding comments for each possible grammatical construct.
After that, identify what kind of restrictions the construct requires you to impose on the context,
and add a constructor that represents the construct along with the necessary restrictions.
It might be more convenient to move from more specific parts to more general parts:
start with types, then move on to expressions, then to statements, and so on.
It is better to avoid trying to represent everything at once and start with a small subset initially,
gradually expanding it to add new language features.

## Encoding functions and predicates and why you might not want to

Sometimes, you might need to define a complex predicate, or set a new index value to be some non-trivial result of a function application.
Since DepTyCheck can't work with types whose indices are set to be the result of a function application:

<!-- idris
{-
-->

```idris
data X : T -> Type where
  ...
  Xk : ... -> X (f x) -- Won't work with DepTyCheck
```

<!-- idris
-}
-->

Alternatively, you might want to specify that a type satisfies a certain predicate.
Since [DepTyCheck can be buggy when it comes to `So` in specifications](https://github.com/buzden/deptycheck/issues/10),
using predicates expressed as a boolean function is not ideal.
Moreover, the use of a predicate expressed in such a manner would lead to brute forcing its value.

One could instead express predicate/function as another type, whose indices are arguments of a function/predicate
(and, in case of a function, the returned value is also an index).
The predicate/function is defined by pattern-matching on the arguments.
The basic idea is that the resulting type should be inhabited iff the predicate is satisfied,
or the function yields a certain result for the provided arguments.
For instance, one can lift addition of natural numbers to a type level the following way:

```idris
data Add : Nat -> Nat -> Nat -> Type where
  AddZ : Add Z n n
  AddS : Add n m k -> Add (S n) m (S k)
```

It is a bit unclear how general this procedure can be.
It seems that all partial recursive functions on naturals numbers can be encoded as types,
hence allowing for encoding of any computation that can be run by a turing-complete model of execution.
There is a strong belief that indexed types can be arithmetised (i. e. allow for an injective computable encoding as natural numbers),
but this is yet to be carefully proven.
If that indeed holds true, this means that the procedure is indeed general enough, at least on paper.

One must remember to caveats when it comes to this encoding:

- Unlike with functions, there will be no "taking the first satisfactory branch of pattern-matching" semantics. Because of this, you
  might need to define pattern-matching more precisely,
- The depth of recursion would be limited by the fuel supplied to the generator. Since large specifications tend to run well on small fuel
  only, you wouldn't be able to define complex predicates or computations.

## Fortunate and unfortunate orderings of generators

DepTyCheck might choose a specific ordering of generators that might lead to a terrible performance.
For instance, it might try to generate a set of fields, and then look through the current context for a class with a specific set.
This would lead the terrible performance, because it is essentially "brute-forcing" the set rather than picking a specific one.

Currently, there is no fix for this issue, but one might try the following:

- Reorder constructor fields
- Move problematic constructor to a separate data structure, and provide handwritten generator
- Come up with a way (perhaps, it could be a part of yet-to-be-developed specification eDSL) that would allow specifying a preferred ordering

## Names vs. de Brujin indices

One would inevitably have to reference the names available in the current context, and this could be generally done in two ways:

- Give a concrete name to each variable when it first introduced
- Reference variables via de Brujin indices and supply names to them during test printing

The first approach would require one to ensure that the names of new variables are unique, which blows up the size of the variable context.
However, using de Brujin's indices seems to be less general, as its naive implementation wouldn't, for example,
allow circular dependencies of class definitions.
Because of this, to tie the recursive knot and avoid working with obnoxious telescopes,
one would have to use something like "bare" natural number to allow circular references.

Because of this caveat, it is not immediately obvious which one should be preferred.
It is suggested to implement two versions of some small specification and comparing generation and derivation time on both.

## `List`- vs. `SnocList`-like representation of programs

One can choose to represent sequences of statements of a language in one of two ways

- `SnocList`-like: Each constructor represents adding corresponding operation to the end of the program
  (recursive part is the prefix of the operation)
- `List`-like: Each constructor represents adding corresponding operation to the beginning of the program
  (recursive part is the suffix of the operation)

Right now, it is not clear which representation is a better one.
It is easier to make some operations "terminal" (disallowing adding anything after them) in `List`-like representation,
while a `SnocList`-like representation feels more natural to the author,
as you impose restrictions and apply new constructors to the context as if you are executing program step-by-step.
There might be some other benefits to each of the representations, and this should be explored further.

## Boolean vs. type-level predicates

Unlike with resulting type, DepTyCheck allows use of functions in indices of arguments of a constructor.
However, it seems like the performance of derivation is poor.
It would be useful to compare both derivation and runtime performance of specifications that use functions vs. type-level encoding.

## Other thoughts and questions

- It seems that generators with less given parameters tend to be more efficient in some cases, due to bigger value range.
  This should be explored and, if it holds, these generators should be prefered.
- Currently, the derivation is performed constructor-wise.
  Can we have a less-local derivation approach where, in case some given parameter is known at derivation time,
  it would statically prune all the empty branches?
  This could improve performance where we derive generators for cases like loop termination conditions,
  where the given arguments are known at derivation time.
