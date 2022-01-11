===========
Limitations
===========

.. todo to add links to `design/...` sections

Temporary design decisions
==========================

Fuel pattern
------------

- explicit fuel pattern of derived gens for totality because ``Gen`` monad is only finite

- explicit fuel pattern is required even for non-recursive data types

Regular parameters
------------------

- all params of derived generators must

  - be omega (runtime)
  - have the same name as such parameter in the original type

Auto parameters
---------------

- only of ``Gen`` type is supported to be in ``auto``-parameters of the derived generators

- external ``Gen`` (passed as ``auto``-parameter) must have the signature of generated one (i.e. fuel pattern, omega, names as in the type, etc.)

Structure of derived generator
------------------------------

- now all derived subgenerators needed for the current type are generated as local functions inside the derived generator function
  even if there are some common generators between different derivation tasks

To be fixed/reworked
====================

- speed of derivation
- polymorphism over types, including external gens over quantified types
- no external ``DecEq``'s yet
- least-effort cons derivator: no support of ordering depending on externals
- GADT structure does not influence on the ordering of cons params generation
- no support for additional ``auto`` arguments of derived gens (even if they are needed for the generated data)
- only constructors (and bare variables) are supported on the RHS of GADTs constructors
