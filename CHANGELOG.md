# Changelog

## 0.0.261115

- Added a simpler way to do probability tuning, using e.g. `%runElab tuneProbability Con (*2)` or `%runElab tuneProbabilities Con1 (*2) Con2 (*3)`

## 0.0.260827

- Automatic specialisation during derivation, supporting nested data types that are not mutually recursive with the target type

## 0.0.260623

- `allDetermValues`, a pure, lazy runner for enumerating deterministic generator values. It skips raw random generators and monadic binds.
  For example:

  ```idris
  values : LazyList Nat
  values = allDetermValues (elements [1, 2, 3]) -- [1, 2, 3]
  ```

- Derivation support for determinable function calls in given arguments and equality checks on complex expressions

## 0.0.251026

- Faster derivation through data structures better suited to the derivator's lookups and collections

## 0.0.250824

- Derivation can generate prerequisite arguments before arguments whose order the user has explicitly requested

## 0.0.250511

- Overhauled the derivation engine into separate stages for types, constructors, and constructor bodies.
  Reflection utilities now live in the separate `elab-util-extra` library

## 0.0.250319

- Structurally decreasing generation no longer consumes fuel, avoiding needless cutoffs when the given indices already bound recursion

## 0.0.250305

- Given and generated type arguments can appear in any order in a derivation request, rather than having to follow the target type's declaration order

## 0.0.250302

- Added constructor probability tuning for derived generators, allowing users to control the distribution without writing generators by hand

- Simplified generator emptiness to `NonEmpty` and `MaybeEmpty`, replacing `MaybeEmptyDeep` with a proof of non-emptiness.
  Code using the old emptiness API needs updating

## 0.0.250213

- Derivation support for primitive values in constructors, including primitive values in type indices

## 0.0.241022

- Added user-provided ordering clues for constructor argument generation.
  For a constructor `MkY` with an argument named `second`:

  ```idris
  GenOrderTuning "MkY".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [`{second}]
  ```

- A multi-stage argument ordering algorithm uses dependencies and determination information to choose generation order for dependent constructors

## 0.0.240909

- Added functions for picking a single random generated value directly. `pick` returns `Nothing` if the attempt produces no value:

  ```idris
  import System.Random.Pure.StdGen

  pickNumber : IO (Maybe Nat)
  pickNumber = pick (elements [1, 2, 3])
  ```

## 0.0.240724

- Added printing derived generators as Idris code for inspection and debugging:

  ```idris
  %runElab deriveGenPrinter $ Fuel -> Gen MaybeEmpty Nat
  ```

- Added model coverage support across the generator runners

## 0.0.220712

- Added static and runtime labels for generators and model coverage reports that show which types and constructors were exercised

- Derivation processes generators one at a time, with cached constructor recursiveness information to reduce repeated computation

- Generator simplification can be tuned at the derivation site.
  Set `simplificationHack` to `True` to keep only the first argument generation order (the default `False` keeps all orders):

  ```idris
  unitGen : Fuel -> Gen MaybeEmpty Unit
  unitGen = deriveGen @{LeastEffort {simplificationHack = True}}
  ```

- Reworked derivation configuration to support `%defaulthint`

- Derived generators reuse internal generators built with the same arguments

- Redesigned generators to unify the separate `Gen` and `Gen1` APIs under `Gen`, with emptiness tracked in its type.
  The emptiness indices introduced here were `NonEmpty`, `MaybeEmptyDeep`, and `MaybeEmpty`;

  ```idris
  nonEmpty : Gen NonEmpty Nat
  nonEmpty = elements [1, 2, 3]

  possiblyEmpty : Gen MaybeEmpty Nat
  possiblyEmpty = empty
  ```
