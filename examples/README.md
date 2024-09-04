# Examples of DepTyCheck usage

Currently, all examples of DepTyCheck library usage are examples of *generation* of values of some types.
Examples of properties and other stuff are to be added as soon as corresponding functionality is implemented in the library.

## Data structures and their generators

Current examples of generation can be globally divided to examples with hand-written generators and with derived generators.
All examples have derived generators unless explicitly mentioned.

All examples are separate projects, which can be build and/or tested independently.
For example, you can run `pack build sorted-list-so-comp` for building one of the sorted lists examples.
Please be aware that derivation process can take some time, up to several minutes.

The examples are the following:

- sorted lists of natural numbers
  - [sorted lists](sorted-list-tl-pred/) with sortedness coded through type-level predicates
  - [sorted lists](sorted-list-so-comp/) with sortedness coded through a type-level predicate using `So` for comparison (gives best distribution)
  - [sorted lists](sorted-list-so-full/) with sortedness coded fully through `So` over boolean predicates
- list and vector of strings, [both with unique elements](uniq-list/) implemented using `So` and usual `Eq` comparison
- a sequence of [unique mentions of a given subset](covering-seq/) of elements interleaved with unrelated elements
- naive possibly empty [sorted binary trees](sorted-tree-naive/) of natural numbers, implemented as if without dependent types
  with added limitations on sortedness
- [indexed non-empty sorted binary trees](sorted-tree-indexed/) of natural numbers, with type indices for value bounds
- [`pil-reg`](pil-reg/), a primitive imperative language with scoped typed variables and typed registers (hand-written generators)
- [`pil-fun`](pil-fun/), a primitive statically-typed imperative language with mutable and immutable variables and nested functions
