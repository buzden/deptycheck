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

data Y : X rc -> X (S rc) -> X rc -> Type where
  MkY : Y (MkX $ f x) (MkX $ FS $ f x) x

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (rc : Nat) -> (r1 : X rc) -> (r2 : X $ S rc) -> (r3 : X rc) -> Gen MaybeEmpty (Y r1 r2 r3)
