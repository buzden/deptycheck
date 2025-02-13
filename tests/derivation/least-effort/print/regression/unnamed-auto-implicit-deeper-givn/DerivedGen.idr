module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data X : Bool -> Type where
  MkX : (b : Bool) -> X b

data Y : Bool -> Type where
  MkY : X b -> X b -> Y b

data Z : Y b -> Type where
  Start : Z y
  Go    : Z (MkY x x1) -> Z (MkY x x2)

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter $ Fuel -> (b : Bool) -> (y : Y b) -> Gen MaybeEmpty $ Z y
