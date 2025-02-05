module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Y : Unit -> Type where
  Z : Y x
  S : Y x -> Y x'

data X : Y () -> Y () -> Type where
  MkX : X a (S a)

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter $ Fuel -> (a, b : Y ()) -> Gen MaybeEmpty (X a b)
