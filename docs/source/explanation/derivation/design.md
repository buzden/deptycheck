# Design of derivation

## Overview

By *derivation* we mean automatic creation of a generator given a datatype definition and,
possibly, some configuration and additional stuff.

:::{todo}
ad hoc a-la staged derivation
:::

:::{note}
We love the idea of truly staged derivation, like described
[in this paper](https://mpickering.github.io/papers/staged-sop.pdf).
However, we don't know yet how this approach works with dependent types,
thus we focus on more ad-hoc direct derivation.
:::

(sect-derivation-task)=

## Derivation task

:::{todo}
We are working in dependently typed context, so in general case generator is a function
rather than just a data instance.

- derivation task (given/generated type arguments, external generators)
  - incl. problem of target type with external generators without fuel pattern
:::

## Type parameters and type indices

:::{todo}
distinction between type parameters and type indices,
relativity of these terms to the derivation task
:::

## Closure of derived generators

:::{todo}
closure of (potentially) mutually recursive generators

- potential caching of generators of common types
:::

## Design of a single generator

:::{todo}
design of single-type generator
:::

## Derivation for a single constructor

:::{todo}
design of constructor derivator, order and staff
:::

### Strategies of constructor derivation

:::{todo}
incl. different strategies of constructor derivators
:::

### Least-effort strategy

:::{todo}
least-effort strategy and the company
:::
