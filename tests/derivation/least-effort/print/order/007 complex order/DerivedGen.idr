module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

g : {n : _} -> Fin n -> Fin n
g = finS

data Y : (n : Nat) -> Fin n -> Type where
  Y1 : Y 1 i
  Y2 : Y 2 1

data Z : Type where
  MkZ : (n : Nat) -> (x : Fin n) -> (y : Y n (g x)) -> Z

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
