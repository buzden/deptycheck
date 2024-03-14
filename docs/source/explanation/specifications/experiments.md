# Experiments

This section presents some simple experiments investigating how the complexity of the generated type affects the derivation time.

## Constructors

In the first experiment, it is found out how the number of constructors affects the derivation time.
A simple type dependent on `Nat` was created. The number of constructors increased with each iteration.
```idris
data SomeType : Nat -> Type where
MkST1: SomeType 0
MkST2: SomeType 0
MkST3: SomeType 0
 -- More constructors ...
```

It turns out that when new constructors are added, derivation time grows linearly.
```
chart
```

## Arguments

In this experiment, the dependence of derivation time on the number of arguments in the constructors is measured.
A type with multiple constructors was created. The number of arguments in the constructors increased with each iteration.
```idris
data A1 : Type where
MkA: A1

data SomeType : Nat -> A1 -> Bool -> Type where
MkST1: (n: Nat) -> (i: A1) -> (b: Bool) -> SomeType n
MkST2: SomeType 0 -- MkST2: (n: Nat) -> (i: A1) -> (b: Bool) -> SomeType n
MkST3: SomeType 0 -- MkST3: (n: Nat) -> (i: A1) -> (b: Bool) -> SomeType n
```

The following chart shows the results.
```
chart
```

## Givens VS Pairs

This experiment tested how givens affect derivation time compared to pairs of types. The idea of the experiment is to try two different generators for the same generated type.

The generated type has only one constructor with no arguments. With each iteration a new `Nat` was added to the signature. The value of `Nat` was always `0` (`Z`) to simplify the type.
```idris
-- data X: Nat -> Type where
-- X1: X 0
data X: Nat -> Nat -> Type where
X1: X 0 0
-- data X: Nat -> Nat -> Nat -> Type where
-- X1: X 0 0 0
```

This is how generator with 2 givens looks like:
```idris
public export
genCustom : Fuel -> (a: Nat) -> (b: Nat) -> Gen MaybeEmpty $ X a b
genCustom = deriveGen
```

And this is the generator with the pair of types:
```idris
public export
genCustom : Fuel -> Gen MaybeEmpty $ (a ** b ** X a b)
genCustom = deriveGen
```

The experiment showed that the derivation time of both types of generators increases linearly. However, the derivation time of generators with givens grows faster.
```
chart
```