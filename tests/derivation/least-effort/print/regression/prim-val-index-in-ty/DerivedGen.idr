module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data X : Int32 -> Type where
  X1  : X 1
  X2  : X 2
  X2' : X 2

data Y : X 2 -> Type where
  MkY : Y X2

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (x : _) -> Gen MaybeEmpty (Y x)
