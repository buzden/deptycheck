module DerivedGen

import AlternativeCore
import PrintDerivation

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

%runElab printDerived @{LeastEffort} $ Fuel -> (x : X) -> (x' : X) -> Gen MaybeEmpty $ Z x x'
