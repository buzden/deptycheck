module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X1 : Nat -> Type where
  MkX1 : (n : _) -> X1 n

data X2 : Nat -> Type where
  MkX2 : (n : _) -> X1 n -> X2 n

data Y : Type where
  MkY : X2 n -> Y

%runElab printDerived @{LeastEffort} $ Fuel -> Gen MaybeEmpty Y
