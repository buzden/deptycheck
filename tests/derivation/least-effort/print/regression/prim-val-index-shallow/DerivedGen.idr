module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Y : Int32 -> Type where
  MkY : Y 1

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (x : _) -> Gen MaybeEmpty (Y x)
