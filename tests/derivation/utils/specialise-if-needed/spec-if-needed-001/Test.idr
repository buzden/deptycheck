module Test

import Shared

%language ElabReflection

%runElab runSIN Nothing False (const "VectNat") `(Vect _ Nat)
