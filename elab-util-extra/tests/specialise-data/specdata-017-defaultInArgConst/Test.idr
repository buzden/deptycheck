module Test

import Shared

%language ElabReflection

data V : Type where
  MkV : (0 n : Nat) -> {default 0 p : Fin (S n)} -> V

%runElab specialiseDataLam' "V'" V

v0 : V'
v0 = MkV 10

v1 : V'
v1 = MkV 10 {p=1}
