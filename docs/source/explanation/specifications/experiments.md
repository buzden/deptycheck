# Experiments

There are many possible ways to change types and derivation tasks.
Some of them are presented on this page.
For the types presented, it's investigated how type complexity affects derivation time.

All experiments were performed with the following settings:

<!-- idris
import Deriving.DepTyCheck.Gen
%hide Deriving.DepTyCheck.Gen.deriveGen

-- a stub pretending it is a derivator
deriveGen : a
-->

<!-- The code block below uses ```<space>idris intentionally, now this code does not compile and it's okay -->
``` idris
%language ElabReflection

%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort {simplificationHack = True}
```

The version of the compiler used is `https://github.com/buzden/Idris2/commit/9ab96dacd4f855674028d68de0a013ac7926c73d`.

Please, notice that used settings may fail typechecking with the most recent versions of the compiler and library.

## Constructors

In the first experiment, it is found out how the number of constructors affects the derivation time.
A simple type dependent on `Nat` was created.
The number of constructors increased with each iteration.

```idris
data SomeType : Nat -> Type where
  MkST1: SomeType 0
  MkST2: SomeType 0
  MkST3: SomeType 0
  -- More constructors ...
```

## Arguments

In this experiment, the dependence of derivation time on the number of arguments in the constructors is measured.
A simple dependent type with one constructor was created.
The number of arguments increased with each iteration.
The derivation task was not changed during the experiment.

```idris
data Args : Nat -> Type where
  MkArgs: (n: Nat) -> (n: Nat) -> Args n
```

```idris
genArgs : Fuel -> Gen MaybeEmpty $ (n ** Args n)
genArgs = deriveGen
```

## Givens vs Pairs

This experiment tested how givens affect derivation time compared to pairs of types.
The idea of the experiment is to try two different generators for the same generated type.

The generated type has only one constructor with no arguments.
With each iteration a new `Nat` was added to the signature.
The value of `Nat` was always `0` (`Z`) to simplify the type.

```idris
data X: Nat -> Nat -> Type where
  X1: X 0 0
```

This is how derivation task with 2 givens:

```idris
genXGivens : Fuel -> (a: Nat) -> (b: Nat) -> Gen MaybeEmpty $ X a b
genXGivens = deriveGen
```

And this is the derivation task with the pair of types:

```idris
genXPairs : Fuel -> Gen MaybeEmpty $ (a ** b ** X a b)
genXPairs = deriveGen
```

## Conclusion

The types used were very simple, so changing them didn't cause a combinatorial explosion.
With each change, the derivation time increased linearly but at different rates.

There is a list of changes ordered by increasing impact on derivation time.

1. Adding a pair of types
2. Adding a given to the derivation task
3. Adding conctructor to the generated type
4. Adding an argument to some constructor of the generated type

There's one more detail. The values that index types also affect the derivation time.
For example, derivation task for `SomeType` indexed by `0` was completed 20 times faster than for indexed by `2147483647`.

<!--- This code takes too long to compile --->
::: {code} idris
data LongNum : Nat -> Type where
  MkLN: LongNum 2147483647
:::
