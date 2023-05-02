<!-- idris
module Explanation.Derivation.Design.SingleGen

import Explanation.Derivation.Design

%language ElabReflection
-->

# Design of a single generator

Generator of a single type simply attempts to call for all possible constructors of this type (in the given context of the derivation task).

:::{note}
This design decision is temporary.
In the future it is planned to be configurable.
For example, one may want to tune possibilities of different constructors.

It is crucial.
Consider derived simple generator for the `Nat` type.
Probability of `Z` and `S` cases are equal.
It means that probabilities of zero and all numbers more than zero (in bounds of given fuel) are equal,
probabilities of `1` and all numbers more than `1` are equal too, and etc.
:::

It is decided that this place is the only where fuel of the fuel pattern is spent.
It means that potentially infinite recursion and empty fuel should be managed only here,
so there is no need to bother on this in functions that generate values for particular constructors.

To make derived generators to be provably total, target datatypes are analysed for recursion.
Non-recursive paths are called always even if given `Fuel` value is `Dry`.
Recursive constructors are called only when `Fuel` can be spent.

So, let's expand the example from [the previous section](closure-of-gens).
These were the data definitions:

```idris
mutual
  data X = X0 | X1 | X2 Y
  data Y = Y0 | Y1 X
```

The following code would be derived:

<!-- idris
namespace SingleGen {
-->
```idris
genX : Fuel -> Gen MaybeEmpty X
genX fuel = data_X fuel
  where
    data_X : Fuel -> Gen MaybeEmpty X
    data_Y : Fuel -> Gen MaybeEmpty Y

    data_X fuel = case fuel of
        Dry    => oneOf [con_X0 Dry, con_X1 Dry]
        More f => oneOf [con_X0 f  , con_X1 f  , con_X2 f]
      where
        con_X0 : Fuel -> Gen MaybeEmpty X
        con_X1 : Fuel -> Gen MaybeEmpty X
        con_X2 : Fuel -> Gen MaybeEmpty X

        con_X0 fuel = ?gen_body_for_constructor_X0
        con_X1 fuel = ?gen_body_for_constructor_X1
        con_X2 fuel = ?gen_body_for_constructor_X2

    data_Y fuel = case fuel of
        Dry    => oneOf [con_Y0 Dry]
        More f => oneOf [con_Y0 f  , con_Y1 f]
      where
        con_Y0 : Fuel -> Gen MaybeEmpty Y
        con_Y1 : Fuel -> Gen MaybeEmpty Y

        con_Y0 fuel = ?gen_body_for_constructor_Y0
        con_Y1 fuel = ?gen_body_for_constructor_Y1
```
<!-- idris
  }
-->
