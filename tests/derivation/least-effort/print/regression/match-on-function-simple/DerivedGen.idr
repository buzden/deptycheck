module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX  : Fin rc -> X rc

namespace F
  export
  f : X rc -> Fin rc
  f (MkX x) = x

data Y : X rc -> X rc -> Type where
  MkY : Y (MkX (f x)) x

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (rc : Nat) -> (r1, r2 : X rc) -> Gen MaybeEmpty (Y r1 r2)
