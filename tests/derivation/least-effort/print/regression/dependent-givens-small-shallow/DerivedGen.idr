module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data X : (n : Nat) -> Fin n -> Type where
  MkX : (n : _) -> (f : _) -> X (S n) (FS f)

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> (f : Fin n) -> Gen MaybeEmpty $ X n f
