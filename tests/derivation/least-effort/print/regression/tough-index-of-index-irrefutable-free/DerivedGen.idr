module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

data Y : Unit -> Type where
  Z : Y x
  S : Y x -> Y x'

data X : Y a -> Y a -> Type where
  MkX : X a (S a)

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter $ Fuel -> {c : _} -> (a, b : Y c) -> Gen MaybeEmpty (X a b)
