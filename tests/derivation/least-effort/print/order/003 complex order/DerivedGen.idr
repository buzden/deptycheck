module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

g : {n : _} -> Fin n -> Fin n
g = finS

data X : (n : Nat) -> Fin n -> Type where
  X0 : X 1 i
  X2 : X 3 2

data Y : (n : Nat) -> Fin n -> Type where
  Y0 : Y 1 i
  Y2 : Y 3 2

data Z : Type where
  MkZ : (n : Nat) -> (i : Fin n) -> (x : X n (g i)) -> (y : Y n i) -> Z

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
