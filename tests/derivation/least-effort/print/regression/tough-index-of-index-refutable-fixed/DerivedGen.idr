module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Y : Bool -> Type where
  Z : Y x
  S : Y x -> Y x'

data X : Y True -> Y True -> Type where
  MkX : X a (S a)

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter $ Fuel -> (a, b : Y True) -> Gen MaybeEmpty (X a b)
