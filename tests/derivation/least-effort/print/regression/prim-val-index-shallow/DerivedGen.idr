module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Y : Int32 -> Type where
  MkY : Y 1

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (x : _) -> Gen MaybeEmpty (Y x)
