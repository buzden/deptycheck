module Test

import Shared

%language ElabReflection

%runElab specialiseData' "MyNat" Nat

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifySpecialisation Nat MyNat
  [ `(0)
  , `(1)
  , `(2)
  , `(5)
  , `(10)
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1' = %runElab verifyNums Nat MyNat [0,1,2,3,4,5]
