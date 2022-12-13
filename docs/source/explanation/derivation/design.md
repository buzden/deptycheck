<!-- idris
module Explanation.Derivation.Design

import public Deriving.DepTyCheck.Gen

%language ElabReflection

-- Empty body derivation
export
DerivatorCore where
  canonicBody sig n = pure [ callCanonic sig n implicitTrue (replicate _ implicitTrue) .= `(empty) ]
-->

# Design of derivation

By *derivation* we mean automatic creation of a generator given a datatype definition and,
possibly, some configuration and additional stuff.

:::{todo}
Almost every section here should have a reference to some section in `reference/contributors` for technical explanations.
:::

```{toctree}
---
caption: Contents
maxdepth: 2
---
design/when-derivation-happens
design/derivation-task
design/type-params-and-indices
design/closure-of-gens
design/single-gen
design/single-con
```
