module Test

import Shared

%language ElabReflection

data X : Nat -> Type where
  MkX : {0 n : Nat} -> {default 0 p : Fin (S n)} -> X (S n)

%runElab specialiseData' "X'" $ X 2

x0 : X'
x0 = MkX

x1 : X'
x1 = MkX {p=1}
