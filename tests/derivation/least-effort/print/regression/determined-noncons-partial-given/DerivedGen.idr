module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data Y : Bool -> Nat -> Type where
  MkY : Y l n

data X : (b : _) -> Y (not b) n -> Type where
  MkX : X b MkY

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (b : _) -> (n : _) -> (y : Y (not b) n) -> Gen0 $ X b y
