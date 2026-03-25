module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX  : Fin rc -> X rc

data Y : (f : (0 r : _) -> X r -> Fin r) -> X rc -> X rc -> Type where
  MkY : Y f (MkX (f rc x)) x

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (rc : Nat) -> (f : (0 r : _) -> X r -> Fin r) -> (r1, r2 : X rc) -> Gen MaybeEmpty (Y f r1 r2)
