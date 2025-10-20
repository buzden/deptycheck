module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\n, a => Vect n a) "MyVect"

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
v0' = %runElab verifySpecialisation (Vect 0 Nat) (MyVect 0 Nat) [`([])]

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
v1' = %runElab verifySpecialisation (Vect 1 Nat) (MyVect 1 Nat)
  [ `( [0] )
  , `( [1] )
  , `( [2] )
  ]

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
v2' = %runElab verifySpecialisation (Vect 1 String) (MyVect 1 String)
  [ `( ["a"] )
  , `( ["b"] )
  ]


%runElab specialiseData' (\a, n => Vect n a) "FlipVect"

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
fv0' = %runElab verifySpecialisation (Vect 0 Nat) (FlipVect Nat 0) [`([])]

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
fv1' = %runElab verifySpecialisation (Vect 1 Nat) (FlipVect Nat 1)
  [ `( [0] )
  , `( [1] )
  , `( [2] )
  ]

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
fv2' = %runElab verifySpecialisation (Vect 1 String) (FlipVect String 1)
  [ `( ["a"] )
  , `( ["b"] )
  ]

