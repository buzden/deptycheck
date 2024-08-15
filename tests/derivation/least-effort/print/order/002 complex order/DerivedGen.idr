module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data BS : (n : Nat) -> Type where
  MkBS : BS n

h : Fin n -> BS n -> BS n
h i MkBS = MkBS

data X : (n : Nat) -> BS n -> Type where
  X0 : X 1 bs
  X2 : X 3 bs

data Y : (n : Nat) -> Fin n -> BS n -> Type where
  Y0 : Y 1 i bs
  Y2 : Y 3 2 bs

data Z : Type where
  MkZ : (n : Nat) -> (i : Fin n) -> (bs : BS n) -> (x : X n (h i bs)) -> (y : Y n i bs) -> Z

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
