module Test

import Shared

%language ElabReflection

%runElab specialiseData' "MyVect" $ \n, a => Vect n a

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
v0' = %runElab verifySpecialisation (Vect 0 Nat) (MyVect 0 Nat) [`([])]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
v0'' = %runElab verifyInvalidConstructors (Vect 0 Nat) (MyVect 0 Nat) [`([0])]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
v1' = %runElab verifySpecialisation (Vect 1 Nat) (MyVect 1 Nat)
  [ `( [0] )
  , `( [1] )
  , `( [2] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
v2' = %runElab verifySpecialisation (Vect 1 String) (MyVect 1 String)
  [ `( ["a"] )
  , `( ["b"] )
  ]


%runElab specialiseData' "FlipVect" $ \a, n => Vect n a

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
fv0' = %runElab verifySpecialisation (Vect 0 Nat) (FlipVect Nat 0) [`([])]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
fv1' = %runElab verifySpecialisation (Vect 1 Nat) (FlipVect Nat 1)
  [ `( [0] )
  , `( [1] )
  , `( [2] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
fv2' = %runElab verifySpecialisation (Vect 1 String) (FlipVect String 1)
  [ `( ["a"] )
  , `( ["b"] )
  ]

