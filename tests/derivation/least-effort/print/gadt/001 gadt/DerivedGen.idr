module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> Gen MaybeEmpty $ Fin n
