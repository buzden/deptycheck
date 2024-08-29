module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X_GADT : Nat -> Nat -> Type where
  MkXG_4 : X_GADT 4 5
  MkXG_5 : {m : _} -> X_GADT 5 m

data Y : Type where
  MkY1 : X_GADT n m -> X_GADT n k -> Y
  MkY2 : X_GADT n m -> X_GADT k m -> Y

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y
