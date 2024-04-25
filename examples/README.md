# Examples of DepTyCheck usage

Currently, all examples of DepTyCheck library usage are examples of *generation* of values of some types.
Examples of properties and other stuff are to be added as soon as corresponding functionality is implemented in the library.

## Data structures and their generators

Current examples of generation can be globally divided to examples with hand-written generators and with derived generators.

All examples are separate project, which can be build and/or tested independently.
For example, you can run `pack build sorted-list` for building the sorted lists example.
Please be aware that derivation process can take some time, up to several minutes.

The examples are the following:

- hand-written generators

  - [`pil-reg`](pil-reg/), The Primitive Imperative Language with scoped typed variables and typed registers

- derived generators

  - [sorted lists](sorted-list/) of natural numbers
  - list and vect of strings, [both with unique elements](uniq-list/) implemented using `So` and usual `Eq` comparison
  - naive possibly empty [sorted binary trees](sorted-tree-naive/) of natural numbers, implemented as if without dependent types
    with added limitations on sortedness
  - [indexed non-empty sorted binary trees](sorted-tree-indexed/) of natural numbers, with direct type indices for value bounds
