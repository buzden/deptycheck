Modules inside this folder are here because several tactics for derivation of particular generators can exist
regarding to how they use externals.

Non-obligatory
--------------

We can imagine one which *does not use externals* during taking a decision on the order.
It uses externals if decided order happens to be given by an external generator,
but is not obliged to use any.
It is seemingly most simple to implement, maybe the fastest and
fits well when external generators are provided for non-dependent types.

Obligatory
----------

One important case would be a tactic which *must use all given external generators*
as soon as it runs into an appropriate type.
Dependent types are important here, i.e. generator ``(a : _) -> (b ** C a b)``
is considered to be a generator for the type ``C``.
The problem with obligatory generators is the following:
some external generators may be incompatible.

E.g. once we have ``(a : _) -> (b ** C a b)`` and ``(a ** b ** C a b)`` at the same time,
once ``C`` is used in the same constructor, we cannot guarantee that we will use both external generators.

The same problem is present once we have external generators for ``(a : _) -> (b : T ** C a b)`` and ``(b : T ** D b)`` at the same time,
and both ``C`` and ``D`` are used in the same constructor with the same parameter of type ``T``,
i.e. when constructor have something like ``C a b -> D b -> ...``.

  *Notice, that this problem does not arise in constructors of type* ``C a b1 -> D b2 -> ...``

In this case, we cannot decide in general which value of type ``T`` to be used for generation is we have to use both generators.
We can either fail to generate a value for such constructor,
or alternatively we can try to match all the generated values of type ``T`` from both generators
using ``DecEq`` and leave only intersection.

Best-effort
-----------

As a solution to problems with obligatory cases, we can try our best and discard some external generators if there is a conflict.
In this situation we can also try to make all the possible combinations to be present in the generated values list.

E.g. when we have external generators ``(a : _) -> (b : T ** C a b)`` and ``(b : T ** D b)`` and
a constructor of form ``C a b -> D b -> ...``, we can use values from both pairs
``(a : _) -> (b : T ** C a b)`` with ``(b : T) -> D b`` and
``(a : _) -> (b : T) -> C a b`` with ``(b : T ** D b)``,
i.e. to use both of external generators to form the generated values list
but not obligatorily all the external generators at the same time.
