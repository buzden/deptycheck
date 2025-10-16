module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\a => Vect 0 a) "Vect0"

e0' : Unit
e0' = %runElab verifySpecialisation (Vect 0 Nat) (Vect0 Nat) [`([])]

e0NoCons : Vect0 Nat -> Nat
e0NoCons [] = 0

%runElab specialiseData' (\a => Vect 2 a) "Vect2"

e1 : List TTImp
e1 =
  [ `([0, 1])
  , `([2, 3])
  , `([2, 1])
  ]

e1' : Unit
e1' = %runElab verifySpecialisation (Vect 2 Nat) (Vect2 Nat) e1

%runElab specialiseData' (\a => Vect a String) "VectString"

e2 : List TTImp
e2 =
  [ `([])
  , `([""])
  , `(["test"])
  , `(["hello", "world"])
  ]

e2' : Unit
e2' = %runElab verifySpecialisation (Vect 0 String) (VectString 0) [`([])]

e2'' : Unit
e2'' = %runElab verifySpecialisation (Vect 1 String) (VectString 1) [`([""]), `(["test"])]

e3''' : Unit
e3''' = %runElab verifySpecialisation (Vect 2 String) (VectString 2) [`(["hello", "world"])]
