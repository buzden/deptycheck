module DerivedGen

import Data.Fin

import Deriving.DepTyCheck.Gen

%default total

data IsFS : Fin n -> Type where
  ItIsFS : IsFS (FS i)

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {n : Nat} -> (v : Fin n) -> Gen MaybeEmpty $ IsFS v
