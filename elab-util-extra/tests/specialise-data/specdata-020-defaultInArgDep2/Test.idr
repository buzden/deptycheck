module Test

import Shared

%language ElabReflection

data Y : Type -> Type where
  MkY : Monoid x => {default neutral p : x} -> Y x

%runElab specialiseData' "Y'" $ Y String

y0 : Y'
y0 = MkY

y1 : Y'
y1 = MkY {p="Hello world"}

%runElab specialiseData' "Y''" $ Y Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifyEmptyType (Y Nat) Y''
