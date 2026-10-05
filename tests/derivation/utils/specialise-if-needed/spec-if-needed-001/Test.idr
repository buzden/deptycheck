module Test

import Shared

%language ElabReflection

%logging "deptycheck.derive.specialisation" 20
%logging "specialiseData.taskFormation" 20

%runElab runSIN Nothing True `(Vect _ Nat)
