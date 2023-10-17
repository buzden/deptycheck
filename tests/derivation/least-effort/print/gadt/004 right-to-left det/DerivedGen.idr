module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : X_GADT 5 m

data X_ADT : Nat -> Nat -> Type where
  MkX : (n : _) -> (m : _) -> X_ADT n m

data Y : Type where
  -- Should be generated left-to-right because of GADT on the left
  MkY_LR : X_GADT n m -> X_ADT n k -> Y
  -- Should be generated right-to-left because of GADT on the right
  MkY_RL : X_ADT n m -> X_GADT n k -> Y

%runElab printDerived @{LeastEffort} $ Fuel -> Gen MaybeEmpty Y
