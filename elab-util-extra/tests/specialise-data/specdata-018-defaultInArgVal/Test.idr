module Test

import Shared

%language ElabReflection

data W : Type where
  MkW : (0 n : Nat) -> (k : Fin (S n)) -> {default k p : Fin (S n)} -> W

%runElab specialiseData' "W'" W

w0 : W'
w0 = MkW 10 5

w1 : W'
w1 = MkW 10 5 {p=1}
