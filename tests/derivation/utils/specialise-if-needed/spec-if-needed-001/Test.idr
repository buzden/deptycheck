module Test

import Shared

%language ElabReflection

%logging "deptycheck.util.specialisation" 20

%runElab runSIN Nothing True `(Vect _ Nat)
