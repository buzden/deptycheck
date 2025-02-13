module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Nat -> Type where
  MkX : (n : Nat) -> X n

data Y : Nat -> Type where
  MkY : X n -> X n -> Y n

data Z : Y n -> Type where
  Start : Z (MkY x x2)
  Go    : Z (MkY x x1) -> Z (MkY x x2)

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter $ Fuel -> (n : Nat) -> Gen MaybeEmpty (y : Y n ** Z y)
