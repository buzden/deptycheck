module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X1 : Nat -> Type where
  MkX1 : (n : _) -> X1 n

data X2 : Nat -> Type where
  MkX2 : (n : _) -> X1 n -> X2 n

data Y : Type where
  MkY : X2 n -> Y

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Y
