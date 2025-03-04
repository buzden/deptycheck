module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total


data X = MkX Int32

data Y : X -> Type where
  MkY : Y (MkX 1)

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (x : _) -> Gen MaybeEmpty (Y x)
