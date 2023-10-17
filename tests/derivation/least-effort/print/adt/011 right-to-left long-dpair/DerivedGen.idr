module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : Nat -> Unit -> Type where
  MkX : {n : _} -> {m : _} -> X n m

data Y : Type where
  MkY : X n m -> Y

%runElab printDerived @{LeastEffort} $ Fuel -> Gen MaybeEmpty Y
