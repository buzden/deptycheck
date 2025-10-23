module Test

import Shared

%language ElabReflection

%runElab specialiseData' "Vect0" (\a => Vect 0 a)

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifySpecialisation (Vect 0 Nat) (Vect0 Nat) [`([])]

e0NoCons : Vect0 Nat -> Nat
e0NoCons [] = 0

%runElab specialiseData' "Vect2" $ \a => Vect 2 a

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1' = %runElab verifySpecialisation (Vect 2 Nat) (Vect2 Nat)
  [ `( [0, 1] )
  , `( [2, 3] )
  , `( [2, 1] )
  ]

%runElab specialiseData' "VectString" $ \a => Vect a String

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e2' = %runElab verifySpecialisation (Vect 0 String) (VectString 0)
  [ `( [] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e2'' = %runElab verifySpecialisation (Vect 1 String) (VectString 1)
  [ `( [""] )
  , `( ["test"] )
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e3''' = %runElab verifySpecialisation (Vect 2 String) (VectString 2)
  [ `( ["hello", "world"] )
  ]
