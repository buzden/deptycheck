module Test

import Shared

%language ElabReflection

data Y : (Type -> Type) -> Type where
  MkY : Functor f => f Nat -> Y f

%runElab specialiseDataLam' "Y'" $ Y List

y0 : Y'
y0 = MkY []

y1 : Y'
y1 = MkY [0,1,2,3]
