module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : {m : _} -> X_GADT 5 m

data Y : Type where
  MkY1 : X_GADT n m -> X_GADT n k -> Y
  MkY2 : X_GADT n m -> X_GADT k m -> Y

%runElab printDerived @{LeastEffort} $ Fuel -> Gen MaybeEmpty Y
