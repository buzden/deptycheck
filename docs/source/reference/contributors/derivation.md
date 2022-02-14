# Derivation internals

:::{todo}
Info on *how* this or that part of the derivation facility is implemented.
Think of useful sections below
:::

## Derivation task

:::{todo}
how derivation task is represented internally
:::

## Closure of generators

:::{todo}
how do we implement closure of derived generators using local `StateT`
:::

## Analysis of data for recursion

:::{todo}
how do we analyse which constructors are (mutually) recursive
:::

## Derivation tuning via parametrisation

:::{todo}
`DerivatorCore` and `ConsDerivator` interfaces, their role and design
:::

## Dependencies calculation

:::{todo}
An approach on how do we analyse which arguments depend on which in constructors
:::

## Ordering in the "least-effort" strategy

:::{todo}
How do we calculate in which order arguments should be generated.
Three phases of generation:

- first right-to-left phase
- left-to-right phase
- second right-to-left phase
:::
