module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : (n : _) -> Fin n -> Type where
  ItIsFS : IsFS (S _) (FS i)

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {n : Nat} -> (v : Fin n) -> Gen MaybeEmpty $ IsFS n v
