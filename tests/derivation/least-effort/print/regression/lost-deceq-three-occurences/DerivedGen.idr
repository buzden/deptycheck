module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

data X : Nat -> Nat -> Nat -> Type where
  MkX : X n n n

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (x1 : Nat) -> (x2 : Nat) -> (x3 : Nat) -> Gen MaybeEmpty $ X x1 x2 x3
