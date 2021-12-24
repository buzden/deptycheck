===========
Limitations
===========

.. todo to add links to `design/...` sections

Temporary design decisions
==========================

- all params of derived generators must be omega (runtime)
- ``Gen`` monad is significantly finite, thus explicit fuel pattern of derived gens for totality

To be fixed/reworked
====================

- speed of derivation
- polymorphism over types, including external gens over quantified types
- no external ``DecEq``'s yet
- least-effort cons derivator: no support of ordering depending on externals
- GADT structure does not influence on the ordering of cons params generation
- no support for additional ``auto`` arguments of derived gens (even if they are needed for the generated data)
- only constructors (and bare variables) are supported on the RHS of GADTs constructors

