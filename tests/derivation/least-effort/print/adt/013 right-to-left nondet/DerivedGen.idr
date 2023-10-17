module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {n : _} -> {m : _} -> X n m

data Y : Type where
  MkY : X n m -> X n k -> Y

%runElab printDerived @{LeastEffort} $ Fuel -> Gen MaybeEmpty Y
