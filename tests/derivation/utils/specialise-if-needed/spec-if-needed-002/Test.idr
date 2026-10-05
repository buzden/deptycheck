module Test

import Shared

%language ElabReflection

%logging "deptycheck.derive.specialisation" 20
%logging "specialiseData.taskFormation" 20

data X : (t : Type) -> (t -> Nat) -> Type where

data Y = MkY (X Nat S)

%runElab runSIN Nothing True `(X Nat S)
