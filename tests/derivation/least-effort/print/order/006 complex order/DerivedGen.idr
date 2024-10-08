module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

f : Nat -> Nat
f = (+2)

g : {n : _} -> Fin n -> Fin n
g = finS

data Y : (n : Nat) -> Fin (f n) -> Type where
  Y0 : Y 0 i
  Y2 : Y 2 2

data Z : Type where
  MkZ : (n : Nat) -> (x : Fin (f n)) -> (y : Y n (g x)) -> Z

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
