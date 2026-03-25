module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX  : Fin rc -> X rc

data Y : (f : X rc -> Fin rc) -> X rc -> X rc -> Type where
  MkY : Y f (MkX (f x)) x

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (rc : Nat) -> (f : X rc -> Fin rc) -> (r1, r2 : X rc) -> Gen MaybeEmpty (Y f r1 r2)
