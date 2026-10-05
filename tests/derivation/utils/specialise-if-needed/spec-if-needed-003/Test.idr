module Test

import Data.Fin
import Shared

%language ElabReflection

%logging "deptycheck.derive.specialisation" 20
%logging "specialiseData.taskFormation" 20


data X : (t : Type) -> (t -> Type) -> Type where

data Y = MkY (X Nat Fin)

%runElab runSIN Nothing True `(X Nat Fin)
