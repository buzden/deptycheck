module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX  : Fin rc -> Fin rc -> X rc

namespace F
  export
  f : X rc -> Fin rc
  f (MkX x y) = x `max` y

  export
  g : X rc -> X rc
  g (MkX x y) = MkX (x `min` y) (x `max` y)

data Y : X rc -> X rc -> Type where
  MkY : Y (MkX (f x) (f $ g x)) x

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (rc : Nat) -> (r1, r2 : X rc) -> Gen MaybeEmpty (Y r1 r2)
