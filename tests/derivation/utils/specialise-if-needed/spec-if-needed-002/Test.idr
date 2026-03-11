module Test

import Shared

%language ElabReflection

%logging "deptycheck.util.specialisation" 20

data X : (t : Type) -> (t -> Nat) -> Type where

data Y = MkY (X Nat S)

%runElab runSIN Nothing True `(X Nat S)
