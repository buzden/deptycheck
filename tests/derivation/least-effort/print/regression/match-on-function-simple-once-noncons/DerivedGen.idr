module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX  : Fin rc -> X rc

DecEq (X n) where
  decEq (MkX l) (MkX r) with (decEq l r)
    decEq (MkX l) (MkX l) | Yes Refl = Yes Refl
    _                     | No contra = No $ \case Refl => contra Refl

namespace F
  export
  f : X rc -> X rc
  f (MkX x) = MkX x

data Y : X rc -> X rc -> Type where
  MkY : Y (f x) x

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (rc : Nat) -> (r1, r2 : X rc) -> Gen MaybeEmpty (Y r1 r2)
