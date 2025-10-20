module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\a => Vect 0 a) "Vect0"

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifySpecialisation (Vect 0 Nat) (Vect0 Nat) [`([])]

e0NoCons : Vect0 Nat -> Nat
e0NoCons [] = 0

%runElab specialiseData' (\a => Vect 2 a) "Vect2"

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
e1' = %runElab verifySpecialisation (Vect 2 Nat) (Vect2 Nat)
  [ `( [0, 1] )
  , `( [2, 3] )
  , `( [2, 1] )
  ]

%runElab specialiseData' (\a => Vect a String) "VectString"

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
e2' = %runElab verifySpecialisation (Vect 0 String) (VectString 0)
  [ `( [] )
  ]

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
e2'' = %runElab verifySpecialisation (Vect 1 String) (VectString 1)
  [ `( [""] )
  , `( ["test"] )
  ]

--- Workaround for https://github.com/idris-lang/Idris2/issues/3651
e3''' = %runElab verifySpecialisation (Vect 2 String) (VectString 2)
  [ `( ["hello", "world"] )
  ]
