module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

f : Nat -> Nat
f = (+2)

data Y : (n : Nat) -> Fin (f n) -> Type where
  Y0 : Y 0 i
  Y2 : Y 2 2

data Z : Type where
  MkZ : (n : Nat) -> (x : Fin (f n)) -> (y : Y n x) -> Z

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
