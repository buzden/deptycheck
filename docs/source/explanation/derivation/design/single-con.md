<!-- idris
module Explanation.Derivation.Design.SingleCon

import Explanation.Derivation.Design

%language ElabReflection
-->

# Derivation for a single constructor

## Simple case

In a simple case when there are no type indices and no dependent types are present,
derived code for generation of a value for a single constructor is also simple.
Generation can be boiled down to calling to subgenerators and then calling the selected constructor.

Let's finish the example from [the previous section](single-gen).

Data definitions were the following:

```idris
mutual
  data X = X0 | X1 | X2 Y
  data Y = Y0 | Y1 X
```

We could derive for them something like this:

<!-- idris
namespace SingleCon_Simple {
-->
```idris
genX : Fuel -> Gen X
genX fuel = data_X fuel
  where
    data_X : Fuel -> Gen X
    data_Y : Fuel -> Gen Y

    data_X fuel = case fuel of
        Dry    => oneOf [con_X0 Dry, con_X1 Dry]
        More f => oneOf [con_X0 f  , con_X1 f  , con_X2 f]
      where
        con_X0 : Fuel -> Gen X
        con_X1 : Fuel -> Gen X
        con_X2 : Fuel -> Gen X

        con_X0 fuel = [| X0               |]
        con_X1 fuel = [| X1               |]
        con_X2 fuel = [| X2 (data_Y fuel) |]

    data_Y fuel = case fuel of
        Dry    => oneOf [con_Y0 Dry]
        More f => oneOf [con_Y0 f  , con_Y1 f]
      where
        con_Y0 : Fuel -> Gen Y
        con_Y1 : Fuel -> Gen Y

        con_Y0 fuel = [| Y0               |]
        con_Y1 fuel = [| Y1 (data_X fuel) |]
```
<!-- idris
  }
-->

As you can see, the power of `Applicative` interface is enough for building more complex generators out of subgenerators.

But, actually, this is the case only when we do not consider dependently typed data.
We have to use monadic interface when some of constructor's arguments depend on each other.

Also, there are issues on non-determinism in the order of such generation, which will be explained [below](sect-cons-order).
Because all of that, and for the sake of simplicity of the derivation mechanism,
actual derived code slightly differ even for the simple case.
The following code would be derived.

<!-- idris
namespace SingleCon_Full {
-->
```idris
genX : Fuel -> Gen X
genX fuel = data_X fuel
  where
    data_X : Fuel -> Gen X
    data_Y : Fuel -> Gen Y

    data_X fuel = case fuel of
        Dry    => oneOf [con_X0 Dry, con_X1 Dry]
        More f => oneOf [con_X0 f  , con_X1 f  , con_X2 f]
      where
        con_X0 : Fuel -> Gen X
        con_X1 : Fuel -> Gen X
        con_X2 : Fuel -> Gen X

        con_X0 fuel = oneOf [ pure X0 ]
        con_X1 fuel = oneOf [ pure X1 ]
        con_X2 fuel = oneOf [ do y <- data_Y fuel
                                 pure $ X2 y ]

    data_Y fuel = case fuel of
        Dry    => oneOf [con_Y0 Dry]
        More f => oneOf [con_Y0 f  , con_Y1 f]
      where
        con_Y0 : Fuel -> Gen Y
        con_Y1 : Fuel -> Gen Y

        con_Y0 fuel = oneOf [ pure Y0 ]
        con_Y1 fuel = oneOf [ do x <- data_X fuel
                                 pure $ Y1 x ]
```
<!-- idris
  }
-->

## Managing type indices

We are working with dependently typed data, which may have type indices.
:::{note}
[Remember](sect-type-indices) that set of available constructors may differ depending on the value of a type index.
Also, particular derivation task may influence in whether or not some type argument would be a type index.
:::

An arbitrary well-typed expression can be on the place of type index in a constructor's definition.
For now, we support only two cases: data constructors and values that are propositionally equal to some other type arguments.

### Data constructor indices

There is no problem or much difference with the simple case from above in the case when type index is a generated value
according to the particular derivation task.
Consider the following indexed data type and a derivation task, where this index is generated.

```idris
data D : Bool -> Type where
  JJ : Nat ->    Nat -> D b
  FN : Nat ->    D b -> D False
  TL : String ->        D True
  TR : String -> D b -> D True
```

<!-- idris
namespace TypIdx_Gend_DerivTask {
-->
```idris
genD_idx_generated : Fuel -> (Fuel -> Gen Nat) => (Fuel -> Gen String) => Gen (b ** D b)
genD_idx_generated = deriveGen
```
<!-- idris
  }
-->

For this derivation task the following generator function would be derived.

<!-- idris
namespace TypIdx_Gend_DerivedExample {
-->
```idris
genD_idx_generated : Fuel -> (Fuel -> Gen Nat) => (Fuel -> Gen String) => Gen (b ** D b)
genD_idx_generated @{data_Nat} @{data_String} fuel = data_D_giv_no fuel
  where
    data_Bool : Fuel -> Gen Bool
    data_D_giv_no : Fuel -> Gen (b ** D b)

    data_Bool fuel = case fuel of
        Dry    => oneOf [con_True Dry, con_False Dry]
        More f => oneOf [con_True f, con_False f]
      where
        con_True  : Fuel -> Gen Bool
        con_False : Fuel -> Gen Bool

        con_True  fuel = oneOf [pure True]
        con_False fuel = oneOf [pure False]

    data_D_giv_no fuel = case fuel of
        Dry    => oneOf [con_JJ Dry, con_TL Dry]
        More f => oneOf [con_JJ f, con_FN f, con_TL f, con_TR f]
      where
        con_JJ : Fuel -> Gen (b ** D b)
        con_FN : Fuel -> Gen (b ** D b)
        con_TL : Fuel -> Gen (b ** D b)
        con_TR : Fuel -> Gen (b ** D b)

        con_JJ fuel = oneOf [ do b  <- data_Bool fuel
                                 n1 <- data_Nat fuel
                                 n2 <- data_Nat fuel
                                 pure (_ ** JJ {b} n1 n2) ]

        con_FN fuel = oneOf [ do n        <- data_Nat fuel
                                 (b ** d) <- data_D_giv_no fuel
                                 pure (_ ** FN {b} n d) ]

        con_TL fuel = oneOf [ do s <- data_String fuel
                                 pure (_ ** TL s) ]

        con_TR fuel = oneOf [ do s        <- data_String fuel
                                 (b ** d) <- data_D_giv_no fuel
                                 pure (_ ** TR {b} s d) ]
```
<!-- idris
  }
-->

You can see that is has the similar structure as the one from the simple case example above
except for the fact that the result of recursive call to the `data_D_giv_no` generator needs to be pattern matched.
All functions for constructor generation have dependent parameter wildcarded since it is fully determined by the constructor's application
and automatically set to constants in constructors `FN`, `TL` and `TR`, and is determined by constructor's argument in the case of `JJ`.

You also can see that the value of the type argument is generated in the most economic way.
When there is no place where to get it, a subgenerator for the `Bool` type is used.
But when the boolean parameter can be acquired from some other generator which produces the dependently typed value,
this parameter is taken from there.
You can see this in the cases for constructors `FN` and `TR`.

But since the target data type has a type argument, we can have a derivation task where this parameter is given, not generated:

<!-- idris
namespace TypIdx_Givn_DerivTask {
-->
```idris
genD_idx_generated : Fuel -> (Fuel -> Gen Nat) => (Fuel -> Gen String) => (b : Bool) -> Gen (D b)
genD_idx_generated = deriveGen
```
<!-- idris
  }
-->

It means that all the internal generators would also have additional argument and the structure of the derived generator would be the following.

<!-- idris
namespace TypIdx_Givn_DerivedStructure_BeforeMatch {
-->
```idris
genD_idx_generated : Fuel -> (Fuel -> Gen Nat) => (Fuel -> Gen String) => (b : Bool) -> Gen (D b)
genD_idx_generated @{data_Nat} @{data_String} fuel b = data_D_giv_b fuel b
  where
    data_D_giv_b : Fuel -> (b : Bool) -> Gen (D b)
    data_D_giv_b fuel b = case fuel of
        Dry    => oneOf [con_JJ Dry b, con_TL Dry b]
        More f => oneOf [con_JJ f b, con_FN f b, con_TL f b, con_TR f b]
      where
        con_JJ : Fuel -> (b : Bool) -> Gen (D b)
        con_FN : Fuel -> (b : Bool) -> Gen (D b)
        con_TL : Fuel -> (b : Bool) -> Gen (D b)
        con_TR : Fuel -> (b : Bool) -> Gen (D b)

        con_JJ fuel b = ?body_for_JJ_cons
        con_FN fuel b = ?body_for_FN_cons
        con_TL fuel b = ?body_for_TL_cons
        con_TR fuel b = ?body_for_TR_cons
```
<!-- idris
  }
-->

Argument `b` here is significantly a type index.
It means that depending on its value, some constructors cannot be generated.

Since, expressions that are used to the type index value in the data definitions are just type constructor,
we can pattern match on them in generators.
We would produce a value for the appropriate value of the given index and produce an empty generator for the rest.
Empty generator is available through function `empty`.

So, the structure of the derived generator with the given type index would be the following for the `D` example.

<!--
// jscpd:ignore-start
-->
<!-- idris
namespace TypIdx_Givn_DerivedStructure_WithMatch {
-->
```idris
genD_idx_generated : Fuel -> (Fuel -> Gen Nat) => (Fuel -> Gen String) => (b : Bool) -> Gen (D b)
genD_idx_generated @{data_Nat} @{data_String} fuel b = data_D_giv_b fuel b
  where
    data_D_giv_b : Fuel -> (b : Bool) -> Gen (D b)
    data_D_giv_b fuel b = case fuel of
        Dry    => oneOf [con_JJ Dry b, con_TL Dry b]
        More f => oneOf [con_JJ f b, con_FN f b, con_TL f b, con_TR f b]
      where
        con_JJ : Fuel -> (b : Bool) -> Gen (D b)
        con_FN : Fuel -> (b : Bool) -> Gen (D b)
        con_TL : Fuel -> (b : Bool) -> Gen (D b)
        con_TR : Fuel -> (b : Bool) -> Gen (D b)

        con_JJ fuel b = ?body_for_JJ_cons

        con_FN fuel False = ?body_for_FN_cons
        con_FN _ _ = empty

        con_TL fuel True = ?body_for_TL_cons
        con_TL _ _ = empty

        con_TR fuel True = ?body_for_TR_cons
        con_TR _ _ = empty
```
<!-- idris
  }
-->
<!--
// jscpd:ignore-end
-->

In this case, generation of non-recursive constructors `JJ` and `TL` is straightforward,
the only difference is that `b` is a function argument, not a result of subgeneration.

Recursive cases are not so easy.
Surely, we can first generate value `b` using derived `data_Bool` generator (as we did before for `JJ` constructor)
and then use `data_D_giv_b` recursively, but this approach as least two drawbacks:
it is not effective (especially when generation for some particular index value is hard) and
it gives strange distribution of generated values.
In this example, constructor `JJ` would appear for both values of argument `b` when all other constructors
will appear only once.

That's why, it is better to reverse the order of generation and to use generator from previous derivation task,
i.e. to generate type index simultaneously with the recursive value of `D`.
So, to derive a generator of type `D` of one derivation task, we need also to do derivation for the same type of another derivation task.
The final structure of the derived generator would be the following.

<!-- idris
namespace TypIdx_Givn_DerivedFinal {
-->
```idris
genD_idx_generated : Fuel -> (Fuel -> Gen Nat) => (Fuel -> Gen String) => (b : Bool) -> Gen (D b)
genD_idx_generated @{data_Nat} @{data_String} fuel b = data_D_giv_b fuel b
  where
    data_Bool : Fuel -> Gen Bool
    data_D_giv_no : Fuel -> Gen (b ** D b)
    data_D_giv_b : Fuel -> (b : Bool) -> Gen (D b)

    data_Bool fuel = ?gen_for_Bool_as_above
    data_D_giv_no fuel = ?gen_for_D_with_no_given_as_above

    data_D_giv_b fuel b = case fuel of
        Dry    => oneOf [con_JJ Dry b, con_TL Dry b]
        More f => oneOf [con_JJ f b, con_FN f b, con_TL f b, con_TR f b]
      where
        con_JJ : Fuel -> (b : Bool) -> Gen (D b)
        con_FN : Fuel -> (b : Bool) -> Gen (D b)
        con_TL : Fuel -> (b : Bool) -> Gen (D b)
        con_TR : Fuel -> (b : Bool) -> Gen (D b)

        con_JJ fuel b = oneOf [ do n1 <- data_Nat fuel
                                   n2 <- data_Nat fuel
                                   pure $ JJ {b} n1 n2 ]

        con_FN fuel False = oneOf [ do n        <- data_Nat fuel
                                       (b ** d) <- data_D_giv_no fuel
                                       pure $ FN {b} n d ]
        con_FN _ _ = empty

        con_TL fuel True = oneOf [ do s <- data_String fuel
                                      pure $ TL s ]
        con_TL _ _ = empty

        con_TR fuel True = oneOf [ do s        <- data_String fuel
                                      (b ** d) <- data_D_giv_no fuel
                                      pure $ TR {b} s d ]
        con_TR _ _ = empty
```
<!-- idris
  }
-->

### Equality of index to another argument

Another important case of type index which is supported by the described derivation mechanism
is when type index is propositionally equal to another type argument.

Consider a type of propositional equality for natural numbers.

```idris
data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN x x
```

:::{note}
This type is a particular case of general propositional equality type `Equal`.
For the moment, we cannot use this type for illustrations, because it is polymorphic on the `Type` argument
which is not yet supported by derivation.
:::

As you can see, there is a single type constructor but it is available not for every combination of type arguments.
For example, type `EqualN 5 5` is inhabited while `EqualN 4 5` is not.

Let us consider different variants of derivation tasks.
As in the previous example, there is no much problem for the case where all type arguments are generated.
Consider the following derivation task.

<!-- idris
namespace Eq_AllGened_DerivTask {
-->
```idris
genEqN_all_gened : Fuel -> (Fuel -> Gen Nat) => Gen (n ** m ** EqualN n m)
genEqN_all_gened = deriveGen
```
<!-- idris
  }
-->

For this case, derivation of a generator is straightforward:

<!-- idris
namespace Eq_AllGened_Derived {
-->
```idris
genEqN_all_gened : Fuel -> (Fuel -> Gen Nat) => Gen (n ** m ** EqualN n m)
genEqN_all_gened @{data_Nat} fuel = data_EqualN_giv_no fuel
  where
    data_EqualN_giv_no : Fuel -> Gen (n ** m ** EqualN n m)
    data_EqualN_giv_no fuel = case fuel of
        Dry    => oneOf [ con_ReflN Dry ]
        More f => oneOf [ con_ReflN f   ]
      where
        con_ReflN : Fuel -> Gen (n ** m ** EqualN n m)
        con_ReflN fuel = oneOf [ do x <- data_Nat fuel
                                    pure (_ ** _ ** ReflN {x}) ]

```
<!-- idris
  }
-->

The fact that we have a dependency of presence of a constructor depending on values of the type arguments does not matter
since we are generating all of them.

No very big deal when one type argument is given and another one is generated being propositionally equal to the given.
Consider we have the following derivation task.

<!-- idris
namespace Eq_LeftGened_DerivTask {
-->
```idris
genEqN_right_gened : Fuel -> (n : Nat) -> Gen (m ** EqualN n m)
genEqN_right_gened = deriveGen
```
<!-- idris
  }
-->

The only difference with the previous one is that one of naturals is simply given rather than generated with an external generator.

<!-- idris
namespace Eq_LeftGened_Derived {
-->
```idris
genEqN_right_gened : Fuel -> (Fuel -> Gen Nat) => (n : Nat) -> Gen (m ** EqualN n m)
genEqN_right_gened @{data_Nat} fuel n = data_EqualN_giv_l fuel n
  where
    data_EqualN_giv_l : Fuel -> (n : Nat) -> Gen (m ** EqualN n m)
    data_EqualN_giv_l fuel n = case fuel of
        Dry    => oneOf [ con_ReflN Dry n ]
        More f => oneOf [ con_ReflN f   n ]
      where
        con_ReflN : Fuel -> (n : Nat) -> Gen (m ** EqualN n m)
        con_ReflN fuel n = oneOf [ do pure (_ ** ReflN {x=n}) ]
```
<!-- idris
  }
-->

:::{note}
Note that when the left type argument is given in the derivation task,
then the right one becomes a type index, since depending on its value type is inhabited or not.
But when the right argument is given, then the left one becomes a type index.

So, which type argument is an index is relative to which type argument is given, i.e. to the derivation task in general.
:::

The hard part with this kind of type index is when all type arguments are given.
So, consider the following derivation task.

<!-- idris
namespace Eq_AllGiven_DerivTask {
-->
```idris
genEqN_all_given : Fuel -> (n, m : Nat) -> Gen $ EqualN n m
genEqN_all_given = deriveGen
```
<!-- idris
  }
-->

The return type contains both given values `n` and `m`,
but (according to the datatype definition) we can use (the only) data constructor `ReflN` only in the case,
when `n` and `m` are propositionally equal.

We could try to match on both arguments recursively and try to cover all cases when both arguments are indeed propositionally equal.
Unfortunately, it does not work for datatypes that contain built-in types like `String` or `Integer` inside;
and more importantly, it cannot work in polymorphic case
(which is not supported yet, but is meant to be supported later, thus used approach should support this case too).

It means that we need to determine propositional equality of given arguments during the generation.
Luckily, there is a standard way of doing so and is depicted with the interface `DecEq` of the standard library.
`DecEq` stands for "decidable (propositional) equality" and contains a function of signature `decEq : (x, y : a) -> Dec (x = y)`
where `Dec` is a standard type for decidable constructive problems.
`Dec a` contains two constructors:
one called `Yes` containing the inhabitant (i.e. a proof presence) of type `a`;
the other called `No` containing the proof of uninhabitance of `a`, i.e. a value of type `Not a` (or, equivalently, `Void -> a`).

It means, that using `DecEq` for the type of propositionally equal given type arguments,
we can universally solve the problem of determining whether can we generate a value of a constructor with propositionally equal type arguments.

For the last derivation task, derived generator would be the following.

<!-- idris
namespace Eq_AllGiven_Derived {
-->
```idris
genEqN_all_given : Fuel -> (Fuel -> Gen Nat) => (n, m : Nat) -> Gen $ EqualN n m
genEqN_all_given @{data_Nat} fuel n = data_EqualN_giv_l_r fuel n
  where
    data_EqualN_giv_l_r : Fuel -> (n, m : Nat) -> Gen $ EqualN n m
    data_EqualN_giv_l_r fuel n m = case fuel of
        Dry    => oneOf [ con_ReflN Dry n m ]
        More f => oneOf [ con_ReflN f   n m ]
      where
        con_ReflN : Fuel -> (n, m : Nat) -> Gen $ EqualN n m
        con_ReflN fuel n m = case decEq n m of
          No  _    => empty
          Yes Refl => oneOf [ pure $ ReflN {x=n} ]
```
<!-- idris
  }
-->

Here all the important stuff in types alignment is done by the `Yes Refl` matching.
It is always possible here because as least one argument of `decEq` is a free variable (in fact, both are),
thus it can be unified with some other expression.
In this example, after matching `Yes Refl` expressions `n` and `m` are unified,
thus the return type of the whole function became `EqualN n n`,
thus giving us an ability to use `ReflN` data constructor with its parameter `x` being set to `n`.

### Superposition of both

We can also consider expressions in type index which are a combination of
arbitrarily deep constructors application and a variable propositionally equal to a part of another type argument.

Consider the following data structure.

```idris
data LT2 : Nat -> Nat -> Type where
  Base :              x `LT2` S (S x)
  Step : x `LT2` y -> x `LT2` S y
```

It denotes to a proof that one natural number is strictly less than another natural number minimum by 2.
You can see that this datatype's second parameter is actually a type index and
the `Base` case has both nested constructors and propositional equality.

Consider the hardest derivation task, the one, where both type arguments are given.

<!-- idris
namespace DeepEq_AllGiven_DerivTask {
-->
```idris
genLT2_all_given : Fuel -> (n, m : Nat) -> Gen $ LT2 n m
genLT2_all_given = deriveGen
```
<!-- idris
  }
-->

<!-- idris
namespace DeepEq_AllGiven_Derivation {
-->
```idris
genLT2_all_given : Fuel -> (n, m : Nat) -> Gen $ LT2 n m
genLT2_all_given fuel n m = data_LT2_given_l_r fuel n m
  where
    data_LT2_given_l_r : Fuel -> (n, m : Nat) -> Gen $ LT2 n m
    data_LT2_given_l_r fuel n m = case fuel of
        Dry    => oneOf [ con_Base Dry n m ]
        More f => oneOf [ con_Base f   n m, con_Step f n m ]
      where
        con_Base : Fuel -> (n, m : Nat) -> Gen $ LT2 n m
        con_Step : Fuel -> (n, m : Nat) -> Gen $ LT2 n m

        con_Base fuel n (S (S m)) = case decEq n m of
          No  _    => empty
          Yes Refl => oneOf [ pure $ Base {x=n} ]
        con_Base _ _ _ = empty

        con_Step fuel n (S m) = oneOf [ do lt <- data_LT2_given_l_r fuel n m
                                           pure $ Step {x=n, y=m} lt ]
        con_Step _ _ _ = empty
```
<!-- idris
  }
-->

As you can see, both approaches to type indices described above, are compatible with each other.

### Other index expressions

Of course, deep constructor application and propositional equality to other type arguments
are not the only possible expression types in type indices.
And of course those two are not the only ones which can be used in automatic derivation.

For example, we can think of an arbitrary (non-reversible in the general case) single-argument function application
as such a supportable expression.
In this case, we can perform filtering of generated data for producibility by the given function.

There are a lot of cases possible to be supported.
This is a point of a future research.
We really want to add support of more such an expressions to widen the class of dependently types data for which automatic derivation works.

(sect-cons-order)=

## Strategies of constructor's arguments derivation

The order of generation of dependently typed arguments of a data constructor is not unambiguously determined by the datatype definition.

Sometimes we have both an ability to generate dependent arguments from right to left and from left to right.
It all becomes much more tricky when a several constructor arguments depend on the same argument:
in this case we may generate first from right to left (with several options) and then from left to right;
or we can generate all from left to right from the beginning.

Also, presence of external generators may influence on the decision of the order of generation.
Consider the following datatype definitions and derivation task:

```idris
data Sub1 : Nat -> Nat -> Type
data Sub2 : Nat -> Nat -> Type

data ND : Type where
  MkND : Sub1 x z -> Sub2 y z -> ND
```

```idris
genND : Fuel -> (Fuel -> Gen (a ** b ** Sub2 a b)) => Gen ND
genND = deriveGen
```

It is an open question whether should be always use given generator for `Sub2`,
which can produce a value for the argument `z` of the constructor `MkND`,
and derive generator `Fuel -> (z : Nat) -> Gen (x ** Sub1 x z)` for `Sub1`.
In this case, we will generate value of `Sub2` first and then a value of `Sub1`.

Or alternatively, we can try to derive generators `Fuel -> (z : Nat) -> Gen (y ** Sub2 y z)`
and `Fuel -> Gen (a ** b ** Sub1 a b)` and to generate arguments of `MkND` in the other way,
ignoring the given external generator.

Or, maybe, we may want to derive a generator that combines both of these approaches.

All these let to an idea that there is no single right strategy for ordering.
We considered at least the following variants to be useful.

- **Non-obligatory strategies**.
  "Non-obligatory" means that some present external generator of some type
  may be ignored even if its type is really used in a generated data constructor.

  - Least-effort non-obligatory tactic is one which *does not use externals* during taking a decision on the order.
    It uses externals if decided order happens to be given by an external generator, but is not obliged to use any.
    It is seemingly most simple to implement, maybe the fastest and
    fits well when external generators are provided for non-dependent types

  - Best effort non-obligatory tactic tries to use as much external generators as possible
    but discards some there is a conflict between them.
    All possible non-conflicting layouts may be produced in the generated values list.

    E.g. when we have external generators `(a : _) -> (b : T ** C a b)` and `(b : T ** D b)` and
    a constructor of form `C a b -> D b -> ...`, we can use values from both pairs
    `(a : _) -> (b : T ** C a b)` with `(b : T) -> D b` and
    `(a : _) -> (b : T) -> C a b` with `(b : T ** D b)`,
    i.e. to use both of external generators to form the generated values list
    but not obligatorily all the external generators at the same time.

- **Obligatory** strategies.
  "Obligatory" means that is some external generator is present and a constructor has
  an argument of a type which is generated by this external generator, it must be used
  in the constructor's generator.

  Dependent types are important here, i.e. generator `(a : _) -> (b ** C a b)`
  is considered to be a generator for the type `C`.
  The problem with obligatory generators is that some external generators may be incompatible.

    E.g. once we have `(a : _) -> (b ** C a b)` and `(a ** b ** C a b)` at the same time,
    once `C` is used in the same constructor, we cannot guarantee that we will use both external generators.

    The same problem is present once we have external generators for `(a : _) -> (b : T ** C a b)` and `(b : T ** D b)` at the same time,
    and both `C` and `D` are used in the same constructor with the same parameter of type `T`,
    i.e. when constructor have something like `C a b -> D b -> ...`.

    Notice, that this problem does not arise in constructors of type `C a b1 -> D b2 -> ...`

  In this case, we cannot decide in general which value of type `T` to be used for generation is we have to use both generators.
  We can either fail to generate a value for such constructor (`FailFast`),
  or alternatively we can try to match all the generated values of type `T` from both generators
  using `DecEq` and leave only intersection (`DecEqConflicts`).

All these strategies differ in possible area of application, in user's expectations on the generated values and on effectiveness of derivation.
At the moment, only least-effort strategy is tries to be implemented since it seemed to be the best for the initial prototype.

### Least-effort strategy

:::{todo}
least-effort strategy and the company
:::
