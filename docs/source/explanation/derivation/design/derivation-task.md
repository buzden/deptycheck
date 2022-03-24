<!-- idris
module Explanation.Derivation.Design.DerivationTask

import Explanation.Derivation.Design

%language ElabReflection
-->

(sect-derivation-task)=

# Derivation task

We call an information given to a request of a DepTyCheck library user for derivation of a generator a *derivation task*.
Technically this request is done through a call to [a macro function](ref-deriveGen) or to [an elaboration script](ref-deriveGenExpr).
This information is technically given through a type signature of the macro result type or an explicit parameter of the elaboration script.
But *semantically* this information contains the following:

- the target, i.e. type or type constructor for which a generator is derived;
- if the target is a type constructor, then for each of its type arguments,
  information of whether the value of it is given or should be generated;
- external subgenerators, i.e. set of derivation tasks whose generators can be looked at the generation-site
  if a value of specific type is needed.

Also, some additional candidates were considered, but were temporarily put to the [backlog](../tbd):

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
