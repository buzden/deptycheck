module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

f : Nat -> Nat
f = (+2)

data Y : (n : Nat) -> Fin n -> Type where
  Y1 : Y 1 i
  Y2 : Y 2 1

data Z : Type where
  MkZ : (n : Nat) -> (x : Fin (f n)) -> (y : Y (f n) x) -> Z

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
