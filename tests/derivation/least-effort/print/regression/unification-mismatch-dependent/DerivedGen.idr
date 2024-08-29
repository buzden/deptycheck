module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data X : Type

data Y : X -> Type where
  MkY : Y x

data X : Type where
  Nil  : X
  Cons : (x : X) -> Y x -> X

data Z : X -> X -> Type where
  MkZ : (prf : Y x) -> Z (Cons x prf) (Cons x prf)

%language ElabReflection

%logging "deptycheck.derive.print" 5
%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (x : X) -> (x' : X) -> Gen MaybeEmpty $ Z x x'
