module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : (n : Nat) -> Nat -> Type where
  X0 : X 1 x
  X2 : X 3 x

data Y : (n : Nat) -> Fin n -> Type where
  Y0 : Y 1 i
  Y2 : Y 3 2

data Z : Type where
  MkZ : (n : Nat) -> (i : Fin n) -> (x : X n (n + 2)) -> (y : Y n i) -> Z

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
