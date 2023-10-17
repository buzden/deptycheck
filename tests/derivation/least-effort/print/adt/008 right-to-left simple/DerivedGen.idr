module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : {n : _} -> X n

data Y : Type where
  MkY : X n -> Y

%runElab printDerived @{LeastEffort} $ Fuel -> Gen MaybeEmpty Y
